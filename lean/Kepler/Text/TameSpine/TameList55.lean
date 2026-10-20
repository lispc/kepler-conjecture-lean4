/-
  Kepler.Text.TameSpine.TameList55 — B1 Tame_list 地基批 55：
  inj_on/UNION 集合面（tamespine-port-plan §4 批次表 B1 行；接续批 54 =
  TameList54.lean，批 54 终点 = HOL :13702；本批起点 = HOL :13703
  `inj_on_union`。行号均按主仓 reference/flyspeck（commit 1ce0353）实测；
  批 54 头注预记 :13703/:13730/:13763/:13772/:13780 五锚点与实测一致，
  零偏移。

  载体侦察裁定（批 54 头注预记面的对拍结论）：

  - **inj_on 载体既档**：`inj_on`（tame_defs.hl:343 逐点双方程形）↦
    `Set.InjOn`（批 2 既档，injOnAlt = inj_on_ALT :459 同型，
    TameList2.lean:360）；UNION/INTER 逐字 core `Set` 面，零新桥。
  - **UNION/INTER 面 core+mathlib 在册（开工三处 grep 已核）**：
    `Set.mem_union`（Mathlib/Data/Set/Basic.lean:587）/
    `Set.mem_union_left`/`Set.mem_union_right`（:573/:576）/
    `Set.union_inter_distrib_right`（:831）`Set.empty_union`（:599）/
    `Set.notMem_empty`（:300，新命名法 notMem 非 not_mem）全在册；
    batteries/core 三处清点无同名异面。
  - **set_of_list 载体既档**：`set_of_list u` ↦ `{x | x ∈ u}`（批 24
    uniqInjOn/elementsOfListPr 同式）。
  - **iota 载体既档**：`iota`（seq.vhl:2670 递归形 `iota m (SUC n) =
    m :: iota (SUC m) n /\ iota m 0 = []`）↦ core `List.range'`（批
    2/19/24 iota/range' 面既档）；`Seq.mem_iota`（seq.vhl:2696
    `i <- iota m n <=> m <= i /\ i < m + n`）↦ core `List.mem_range'_1`
    （`m ∈ range' s n ↔ s ≤ m ∧ m < s + n`，
    Init/Data/List/Nat/Range.lean:40）——语句逐字同构零换装（HOL
    EXTENSION/IN_ELIM_THM/IN_SET_OF_LIST 三发的 Lean 面 = 一发 ext）。
  - **BIJ 载体既档**：`BIJ f s t`（INJ+SURJ 复合）↦ `Set.BijOn`
    （MapsTo/InjOn/SurjOn 三槽，Mathlib/Data/Set/Function.lean:617
    BijOn.mk 匿名构造槽）；`inj_on_BIJ` :3317 ↦ 批 4 injOnBijOnImage
    （TameList4.lean:664 既档，SurjOn 槽 Set.mem_image 全显式参体例）。
  - **uniq_inj_on 既档**：:10752 ↦ 批 24 uniqInjOn（TameList24.lean:221，
    BEq/LawfulBEq/Nonempty 约束面）——InjOn+MAP 双支证人形与 HOL
    `?f. inj_on f (set_of_list u) /\ v = MAP f u` 逐字同构，uniq_bij_map
    直接消费（HOL 证体 uniq_inj_on+SET_OF_LIST_MAP+inj_on_BIJ 链的
    Lean 面一步化为 BijOn 三槽组装）。

  新雷区（本批实测记档）：
  - **`rw [hdisj] at h0` 的 Set 等式换装安全例**：`s ∩ t = ∅` 形整应用
    匹配（h0 : y ∈ s ∩ t → y ∈ ∅ 一发干净）不踩「rw 子项等式 at 毒化」
    雷——毒化面是子项等式（部分匹配），整集合等式逐字匹配安全（批 54
    「rw 子项等式 at 毒化走整应用匹配」雷的正例面记档）；
  - **classical 证人 `if x ∈ s then _ else _` 的 beta 未展开面**：
    refine ⟨fun x => if …, ?_, …⟩ 后逐点方程槽内目标保持 lambda 应用形
    （beta 不自动），`simp only [if_pos hx]`/`simp only [if_neg hys]`
    依假设分理发（simp 先 beta 再重写，rw 不然——if_pos 走 rw 须先
    show beta 换面；本批一律 simp only 直落）；InjOn 槽内 hxy 同理
    `simp only [if_pos/if_neg …] at hxy` 换装。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:13703-:13797，六件
  + 二零镜像记档；越章随收 :13856 一件）：

  §1 inj_on union 章：`inj_on_union` :13703-:13728 ↦ injOnUnion（真证；
    证人 `fun x => if x ∈ s then fs x else ft x`（HOL TYPED_ABBREV
    `f = (\x. if (x IN s) then fs x else ft x)` 逐句镜像，classical
    propDecidable 槽）；inj 支四分流 s/s、s/t、t/s、t/t（HOL
    ASM_MESON_TAC 面的 Lean 显式展开：s/s 支 hfs 直投、t/t 支 hft
    直投、s/t 与 t/s 支 cross 前提 absurd 反演 + mem_union 免 SET_TAC
    换装），t 支 disjoint 消费 s∩t=∅；逐点双方程支 if_pos/if_neg 直落
    ——即 HOL FULL_EXPAND_TAC "f" + ASM_SIMP_TAC 面）。
  §2 三族版：`inj_on_union3` :13730-:13761 ↦ injOnUnion3（真证；HOL
    两步复合逐句镜像——先 injOnUnion (fs1,fs2,s1,s2) 得 f，再
    injOnUnion (f,fs3,s1∪s2,s3) 得 f'；中转槽 disjoint (s1∪s2)∩s3=∅
    经 union_inter_distrib_right + h13/h23 + empty_union 三发（HOL
    SET_TAC 面的 rw 显式展开）；cross 槽 f x 经首步逐点方程 hfs1/hfs2
    换装后回喂 hc13/hc23；尾段 s1/s2 逐点方程经 mem_union_left/right
    定位 + 首步方程链二发收口）。
  §3 `INJ_inj_on` :13763 零镜像记档（不落件）：INJ 家族载体折算既例
    （批 2 INJ_inj_on :468、批 4 inj_on_INJ :3308 同例）——`INJ f s t`
    ↦ `Set.InjOn f s ∧ f '' s ⊆ t` 折算下本件 = And.left 投影，零证明
    内容；批 54 头注预记「大概率零镜像跳过」命中。另记：HOL
    tame_list.hl 存在同名 `INJ_inj_on` 两条（:468 旧形
    `inj_on f s <=> INJ f s (:UNIV)` 被本条 :13763 新形
    `INJ f s t ==> inj_on f s` 遮蔽——HOL Light 后定义覆盖；批 2 已按
    旧形折算记档，本条按新形折算记档，两形均零镜像）。
  §4 `set_of_list_iota_alt` :13772-:13778 ↦ setOfListIotaAlt（零镜像
    直投；set_of_list/range'/mem_range'_1 三载体既档，ext 一发）。
  §5 `uniq_bij_map` :13780-:13795 ↦ uniqBijMap（真证；消费批 24
    uniqInjOn 双支证人 + BijOn 三槽组装——MapsTo 槽 v = MAP f u 换装
    （rw hmap）+ show 换 setOf 面 + memfMap（批 2 既档）直投；
    SurjOn 槽 mem_map 反演 + ⟨x,hx,hxy⟩ image 匿名构造直投（批 4
    injOnBijOnImage 同式））。
  §6 边界随收二件：`FST_o_FST` :13797-:13803 ↦ fstOFst（funext + beta/
    投影 rfl，零内容组合子件）；越章随收 `indexToVertexList_nil`
    :13856-:13863 ↦ indexToVertexListNil（载体批 4 既档——
    Kepler.Graphs.indexToVertexList 定义展开 + hideDupsEqNil（批 4
    :141）+ List.map_eq_nil_iff 三发；Face/Vertex 全限定既例）。
  记档二件（零镜像不落）：`hideDups_nil` :13848-:13854 = 批 4
    hideDupsEqNil（TameList4.lean:141 语句逐字同构 `hideDups vv = [] ↔
    vv = []`）；`INJ_inj_on` :13763（§3 如上）。

  诚实记账：六件全真证（injOnUnion/injOnUnion3/setOfListIotaAlt/
  uniqBijMap/fstOFst/indexToVertexListNil），零 sorry、零止损件、
  零记账债、零新 def；setOfListIotaAlt 为零镜像直投件（三载体在册，
  非止损）。
  范围决策：批 55 射程收口至 :13797（UNION 集合面 + iota/BIJ 随收 +
  FST_o_FST 组合子件 + 越章随收 indexToVertexList_nil——自然边界：
  下一件 :13805 `final_list_snd_is_fst` 起为 final_list/normal_list
  新章）。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 56 接续点：HOL :13805 `final_list_snd_is_fst`（:13805-:13829，
  final_list 面——`final_list L r = all (\d. f_list L d = next_el r d) r`
  （tame_defs2.hl:142）；载体 FinalListSpine/finalListSpine 批 31 既档
  （定义形即逐点 ∀∈，TameList31.lean:36 记档），normal_list 载体
  NormalListSpine（批 5 TameList5.lean:127，GoodList 参化形）与 HOL
  `normal_list L N /\ all uniq L` 前提形的对拍开工先核；f_list_fst_snd
  :6702 ↦ 批 10 fListFstSnd（TameList10.lean:319，list_of_darts 面）；
  mem_flatten 槽 = List.mem_flatten（批 52 既档）、mem_next_el 槽
  公开件在册性先核（批 3 memNextEl 为 private）。其后 :13831
  is_restricted_size_face（is_restricted/List_hypermap 面——
  mem_face_lemma/card_face_of_list/dart_hypermap_of_list 载体先核）、
  :13865 enumerator_nil（enumerator 载体 enumAppend/enumBase/POWER
  不在册先核）、:13875 filter_replace（replace 载体不在册先核）、
  :13900 snd_setFinal（FORALL_PAIR_THM 面语句形先核）。
-/

import Kepler.Text.TameSpine.TameList54

namespace Kepler.Text.TameSpine

open Kepler.Graphs (hideDups indexToVertexList)

variable {α : Type*}

/-! ### §1 inj_on union 章（tame_list.hl:13703/:13730） -/

/-- **HOL `inj_on_union`**（tame_list.hl:13703-:13728
`!fs ft s t. inj_on fs s /\ inj_on ft t /\ (s INTER t = {}) /\
(!x y. x IN s /\ y IN t ==> ~(fs x = ft y)) ==> (?f. inj_on f (s UNION t) /\
(!x. x IN s ==> f x = fs x) /\ (!y. y IN t ==> f y = ft y))`）。
证体：证人 `fun x => if x ∈ s then fs x else ft x`（HOL TYPED_ABBREV
逐句镜像，classical 槽）；inj 支四分流（s/s hfs 直投、t/t hft 直投、
s/t 与 t/s 支 cross 前提 absurd 反演，mem_union 免 SET_TAC 换装）；
逐点双方程支 if_pos/if_neg 直落。 -/
theorem injOnUnion {β : Type*} {fs ft : α → β} {s t : Set α}
    (hfs : Set.InjOn fs s) (hft : Set.InjOn ft t) (hdisj : s ∩ t = ∅)
    (hcross : ∀ x ∈ s, ∀ y ∈ t, fs x ≠ ft y) :
    ∃ f : α → β, Set.InjOn f (s ∪ t) ∧ (∀ x ∈ s, f x = fs x) ∧
      (∀ y ∈ t, f y = ft y) := by
  classical
  refine ⟨fun x => if x ∈ s then fs x else ft x, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxs : x ∈ s
    · by_cases hys : y ∈ s
      · simp only [if_pos hxs, if_pos hys] at hxy
        exact hfs hxs hys hxy
      · simp only [if_pos hxs, if_neg hys] at hxy
        exact absurd hxy
          (hcross x hxs y (((Set.mem_union _ _ _).mp hy).resolve_left hys))
    · by_cases hys : y ∈ s
      · simp only [if_neg hxs, if_pos hys] at hxy
        exact absurd hxy.symm
          (hcross y hys x (((Set.mem_union _ _ _).mp hx).resolve_left hxs))
      · simp only [if_neg hxs, if_neg hys] at hxy
        exact hft ((((Set.mem_union _ _ _).mp hx).resolve_left hxs))
          ((((Set.mem_union _ _ _).mp hy).resolve_left hys)) hxy
  · intro x hx
    simp only [if_pos hx]
  · intro y hy
    by_cases hys : y ∈ s
    · have h0 : y ∈ s ∩ t := ⟨hys, hy⟩
      rw [hdisj] at h0
      exact absurd h0 (Set.notMem_empty y)
    · simp only [if_neg hys]

/-- **HOL `inj_on_union3`**（tame_list.hl:13730-:13761 三族版两步复合
`!fs1 fs2 fs3 s1 s2 s3. inj_on fsi si /\ (sj INTER sk = {}) /\
(!xi xj. … ==> ~(fsi xi = fsj xj)) ==> (?f. inj_on f (s1 UNION s2 UNION s3)
/\ …)`）。证体：HOL 两步复合逐句镜像——先 injOnUnion (fs1,fs2,s1,s2)
得 f，再 injOnUnion (f,fs3,s1∪s2,s3) 得 f'；中转槽 disjoint 经
union_inter_distrib_right + h13/h23 + empty_union 三发；cross 槽经首步
逐点方程换装回喂；尾段逐点方程 mem_union_left/right 定位二发收口。 -/
theorem injOnUnion3 {β : Type*} {fs1 fs2 fs3 : α → β} {s1 s2 s3 : Set α}
    (h1 : Set.InjOn fs1 s1) (h2 : Set.InjOn fs2 s2) (h3 : Set.InjOn fs3 s3)
    (h12 : s1 ∩ s2 = ∅) (h23 : s2 ∩ s3 = ∅) (h13 : s1 ∩ s3 = ∅)
    (hc12 : ∀ x ∈ s1, ∀ y ∈ s2, fs1 x ≠ fs2 y)
    (hc13 : ∀ x ∈ s1, ∀ y ∈ s3, fs1 x ≠ fs3 y)
    (hc23 : ∀ x ∈ s2, ∀ y ∈ s3, fs2 x ≠ fs3 y) :
    ∃ f : α → β, Set.InjOn f (s1 ∪ s2 ∪ s3) ∧ (∀ x ∈ s1, f x = fs1 x) ∧
      (∀ x ∈ s2, f x = fs2 x) ∧ (∀ x ∈ s3, f x = fs3 x) := by
  obtain ⟨f, hf, hfs1, hfs2⟩ := injOnUnion h1 h2 h12 hc12
  have hdisj : (s1 ∪ s2) ∩ s3 = ∅ := by
    rw [Set.union_inter_distrib_right, h13, h23, Set.empty_union]
  have hcross : ∀ x ∈ s1 ∪ s2, ∀ y ∈ s3, f x ≠ fs3 y := by
    intro x hx y hy
    rcases ((Set.mem_union _ _ _).mp hx) with hx1 | hx2
    · rw [hfs1 x hx1]
      exact hc13 x hx1 y hy
    · rw [hfs2 x hx2]
      exact hc23 x hx2 y hy
  obtain ⟨f', hf', hfs12, hfs3⟩ := injOnUnion hf h3 hdisj hcross
  refine ⟨f', hf', ?_, ?_, hfs3⟩
  · intro x hx
    rw [hfs12 x (Set.mem_union_left s2 hx), hfs1 x hx]
  · intro x hx
    rw [hfs12 x (Set.mem_union_right s1 hx), hfs2 x hx]

/-! ### §2 set_of_list iota 面（tame_list.hl:13772；INJ_inj_on :13763
零镜像记档见头注 §3） -/

/-- **HOL `set_of_list_iota_alt`**（tame_list.hl:13772-:13778
`!m n. set_of_list (iota m n) = {i | m <= i /\ i < m + n}`）。
载体：`iota m n` ↦ core `List.range' m n`（批 2/19/24 既档），
`Seq.mem_iota` ↦ core `List.mem_range'_1`（语句逐字同构）——
HOL EXTENSION/IN_ELIM_THM/IN_SET_OF_LIST 三发的 Lean 面 = 一发 ext。 -/
theorem setOfListIotaAlt (m n : ℕ) :
    {x | x ∈ List.range' m n} = {i | m ≤ i ∧ i < m + n} := by
  ext i
  exact List.mem_range'_1

/-! ### §3 uniq_bij_map（tame_list.hl:13780） -/

/-- **HOL `uniq_bij_map`**（tame_list.hl:13780-:13795
`!u v. sizel u = sizel v /\ uniq u /\ uniq v ==> (?f. BIJ f
(set_of_list u) (set_of_list v) /\ v = MAP f u)`）。证体：消费批 24
uniqInjOn 双支证人 + `Set.BijOn` 三槽组装——MapsTo 槽 v = MAP f u
换装 + memfMap（批 2 既档）直投；SurjOn 槽 mem_map 反演 + image 匿名
构造直投（批 4 injOnBijOnImage 同式）；HOL SET_OF_LIST_MAP/inj_on_BIJ
链的 Lean 面一步化。 -/
theorem uniqBijMap [BEq α] [LawfulBEq α] {β : Type*} [Nonempty β]
    {u : List α} {v : List β} (hlen : u.length = v.length)
    (hu : u.Nodup) (hv : v.Nodup) :
    ∃ f : α → β, Set.BijOn f {x | x ∈ u} {x | x ∈ v} ∧ v = List.map f u := by
  obtain ⟨f, hinj, hmap⟩ := uniqInjOn hlen hu hv
  refine ⟨f, ⟨?_, hinj, ?_⟩, hmap⟩
  · intro x hx
    rw [hmap]
    show f x ∈ List.map f u
    exact memfMap hx
  · intro y hy
    rw [hmap] at hy
    have hy' : y ∈ List.map f u := hy
    rcases List.mem_map.mp hy' with ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩

/-! ### §4 边界随收（tame_list.hl:13797/:13856） -/

/-- **HOL `FST_o_FST`**（tame_list.hl:13797-:13803
`!f g. FST o (\u. f (FST u),g u) = f o FST`）。零内容组合子件：
funext + beta/投影 rfl（HOL FUN_EQ_THM/o_THM 两发的 Lean 面）。 -/
theorem fstOFst {β γ : Type*} (f : α → γ) (g : α × β → γ) :
    Prod.fst ∘ (fun u : α × β => (f u.1, g u)) = f ∘ Prod.fst :=
  funext fun _ => rfl

/-- **HOL `indexToVertexList_nil`**（tame_list.hl:13856-:13863
`!f v is. indexToVertexList f v is = [] <=> is = []`）。载体批 4 既档
（Kepler.Graphs.indexToVertexList 定义展开）+ hideDupsEqNil（批 4，
即 HOL hideDups_nil :13848 零镜像记档件）+ List.map_eq_nil_iff 三发
（HOL indexToVertexList/hideDups_nil/MAP_EQ_NIL 链逐句镜像）。 -/
theorem indexToVertexListNil (f : Kepler.Graphs.Face) (v : Kepler.Graphs.Vertex)
    (is : List ℕ) : indexToVertexList f v is = [] ↔ is = [] := by
  rw [indexToVertexList, hideDupsEqNil, List.map_eq_nil_iff]

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；六件正文 + 消费链槽全绿零 sorryAx——
#print axioms Kepler.Text.TameSpine.injOnUnion
#print axioms Kepler.Text.TameSpine.injOnUnion3
#print axioms Kepler.Text.TameSpine.setOfListIotaAlt
#print axioms Kepler.Text.TameSpine.uniqBijMap
#print axioms Kepler.Text.TameSpine.fstOFst
#print axioms Kepler.Text.TameSpine.indexToVertexListNil
-/
