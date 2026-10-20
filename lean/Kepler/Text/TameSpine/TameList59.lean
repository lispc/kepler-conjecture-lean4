/-
  Kepler.Text.TameSpine.TameList59 — B1 Tame_list 地基批 59（tame_list.hl
  收官批）：list_update/mapAt 章首 + vertices_set2 + replace/cat 家族 +
  尺寸面 + iso_list 尾章 + 收官四件（tamespine-port-plan §4 批次表 B1 行；
  接续批 58 = TameList58.lean，批 58 终点 = HOL :14208
  （countVertices_makeFaceFinal）；本批起点 = HOL :14211
  `size_list_update`，收口至文件末 :14428。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测；批 58 尾注预记 :14211 与实测
  一致，零偏移。

  ┌─ 整本战绩小结（tame_list.hl 收官，起 :1 至 :14428）─────────────
  │ 实测主定理 649 枚（`prove_by_refinement` 全量清点；任务书口径
  │ 「650 定理」与实测差一枚，记勘误——另含 :19 POWER_TO_ITER/:21
  │ EQ_EXPAND 两枚跨模块别名 let 与 :1397 lower_case/:1401
  │ upper_case/:1469 indexf/:2940 image_hideDups 等定义/别名层）。
  │ B1 线批 1-59 五十九批接续覆盖 :23-:14428 零缺口（批 13/14 头注
  │ 锚「:23-:9125 无缺口」；批 59 收口末段 :14211-:14428）。
  │ 载体约定（批 1-13 立定，全本通用）：`sizel` ↦ `List.length`、
  │ `cat` ↦ `++`、`uniq` ↦ `List.Nodup`、`all uniq L` ↦
  │ `∀ l ∈ L, l.Nodup`、`indexl` ↦ `List.idxOf`、`HD`/`LAST`/`TL` ↦
  │ `head!`/`getLast!`/`tail`、`EL` ↦ `getElem`、`flatten` ↦
  │ `List.flatten`、`hypermap_of_list` ↦ `TameLp.hypermapOfList`
  │ （GoodList 证人为显式参——HOL 原句无此前提，逐件记账）。
  │ 越章随收与记档不落散见各批头注（本批再记两枚，见 §7）。
  │ 下一领土：tame/ 目录全量 64 文件（reduction1.hl 4976 行、
  │ more_tame_concl.hl 等）——B1 线后续章起点由编排者按
  │ tamespine-port-plan §4 裁定。
  └──────────────────────────────────────────────────────────────

  载体侦察裁定（批 58 尾注预记面的对拍结论）：

  - **list_update 载体命中**（批 58 预记「不在册先核，List.set 候选
    对拍」命中）：HOL `list_update`（tame_defs2.hl:194-:197，cons 方程
    `i=0 → v::xs / else x::list_update xs (i-1) v`）↦ Lean 核心
    `List.set`（`set [] _ _ = []`、`set (x::xs) 0 a = a :: xs`、
    `set (x::xs) (n+1) a = x :: xs.set n a`）——语义逐点一致（nat 截断
    减法在 else 支与 n+1 匹配同面），载体对拍记档非止损。
  - **mapAt/replacefacesAt 既档 + 长度件在册命中**：`mapAt`
    （tame_defs2.hl:199-:202）↦ `Kepler.Graphs.mapAt`
    （ListAux.lean:61，dif 形逐字同构）；`replacefacesAt`
    （tame_defs2.hl:278-:279）↦ `Kepler.Graphs.replacefacesAt`
    （FaceDivision.lean:17，Face 特化形——HOL 泛 A 形按 AFP 层实例化，
    泛形机制面由在册 `Kepler.Graphs.length_mapAt`
    （ListAuxLemmas.lean:814，「ListAux.thy: length_mapAt」）覆盖，
    本批主件一发直投零私件。
  - **vertices_set2 新章裁定**：HOL `vertices_set2`（tame_defs.hl:392-:394
    `set_of_list (vertices_graph g)`，vertices_graph = upt 0
    (countVertices g)）↦ 新 def `VerticesSet2Spine g := {v | v <
    g.countVertices}`——iota/set_of_list 集合化定义形 collapse（HOL
    证体 REWRITE 四连 + ARITH_TAC 即此面；Kepler.Graphs.Graph.vertices
    = List.range countVertices 同层互证），vertices_set2_countVertices
    即定义性 Iff.rfl。
  - **replace 家族载体在册**：`replace`（tame_defs.hl:317-:320）↦ 批 17
    `replaceSpine`（TameList17.lean:75，泛 α 形）——replace_id/replace_hd/
    replace_cat2 泛形直投；cat/HD/TL/MEM ↦ `++`/`head!`/`tail`/`∈`。
    批 58 私件 replaceSpineMiss 不可跨模块，本批 replace_id 按公开件
    同证重推导（批 7→8→… 惯例，三行归纳）。
  - **list_of_faces/size_list_pairs 全命中**：`list_of_faces`
    （list_hypermap-compiled.hl:26 `MAP list_pairs L`）↦ 批 31
    `listOfFaces`（TameList31.lean:100，逐字同形）；`size_list_pairs` ↦
    `TameLp.la7_length_listPairs`（批 14 头注预记「按 getElem 折算」
    面，泛 α 形）——MAP_EQ 面两发收口。
  - **iso_list 方向对拍命中**（批 58 预记「IsoListSpine 批 1 方向对拍
    先核」命中）：`IsoListSpine L₁ L₂ N N' := ∃ phi, (InjOn phi
    (elementsOfList L₁) ∧ L₂ = MAP MAP phi L₁ ∧ …)`（TameList1.lean:67，
    第二参数是像）——HOL `iso_list (L',[]) (L,[])` ↦
    `IsoListSpine L' L [] []`，语句逐字同向零换向。iso_list_snd 链件：
    `iso_list_sym_nil`（tame_list.hl:3701）↦ 批 4 `isoListSpineSym`
    空表真空前提形（免批 5 SymNil 形的 GoodList 前提）；`iso_list_trans`
    （more_tame_concl.hl:153）↦ 批 4 `isoListSpineTrans` 在册直投。
  - **is_restricted/simple_hypermap/good_list_nodes 全在册**：
    `is_restricted`（hypermap.hl:11174）↦ `Hypermap.IsRestricted`
    （Hypermap.lean:9645，`.simple` 第五合取项直取）；`simple_hypermap`
    ↦ `Hypermap.Simple`（:1058）；`good_list_nodes` ↦
    `TameLp.GoodListNodesTl`（TameLp.lean:4083，批 11/14 惯例形）；
    `simple_hypermap_uniq`（tame_list.hl:9254）↦ 批 14
    `simpleHypermapUniq` 在册直投。
  - **foldr_size_max/iso 尾章杂项**：`foldr maxn 0` ↦
    `List.foldr max 0`、`MAP sizel` ↦ `map List.length`；`all uniq` 形
    见上。`map_id_eq` 的 HOL 语句 g 为自由变元（隐式全称），Lean 面
    显式入 binder（记账）。

  新雷区（本批实测记档）：
  - **HOL replace 第二参即替换表非元素**：`replace x ys (z::zs) =
    if z = x then APPEND ys zs else …`（tame_defs.hl:317-:320）——ys
    是 LIST（被换入的整段）；若按「b 为元素」误读会把 replace_id/
    replace_hd/replace_cat2 的 b/f 写成元素级 `α` 致 HAppend 型错/
    单表包装错觉（本批三件初稿踩墙后按定义实测定型：b/f 皆
    `List α`，与 replaceSpine 逐槽对齐零包装）。
  - **head! 载体须 [Inhabited α] 实例参**：catToFst/replaceHd 语句面
    `b.head!` 的实例合成失败（Inhabited α）会被 elaborator 静默
    sorry 化（goal 面显示 `x = sorry`，构建报 introN no-binders 类
    连锁错）——须在语句显式加 `[Inhabited α]`（memHd
    TameList2.lean:199 先例体例）；cons 支 `b ≠ []` 证人用
    `List.cons_ne_nil`——rfl 打不进 Ne（蕴涵形非 defeq）。
  - **induction 对上下文前提的自动回填**：`h : x ∈ s`/`h : x ∉ u`
    随 `induction s/u` 自动逐支回填（context 面已见 h）——cons 支
    勿再 `intro h`（introN 报 no-binders 连锁错）；批雷区「induction
    自动 revert 依赖假设 ih 显式回喂」的对偶面：前提在语句 → 后
    （h 已 intro）时自动回填，在上下文时 revert。
  - **rw 链尾 append 残面 auto-rfl 不可达**：`(y :: ys) ++ w` 经
    ih 重写后残面 `y :: (ys ++ w) = (y :: ys) ++ w` 不被 rw 尾置
    rfl 关闭（reducible 透明度不走 List.append delta-iota）——
    `List.cons_append` 入链一发收口（勿赌裸 rfl 后置，若 rw 已闭
    会报 no goals 双向不稳）。
  - **flatten_nil at-换装走显式两步**：isoListSnd 真空前提
    `q ∈ List.flatten []` 面不用 by simp（依赖 simp 集合面不稳），
    `rw [List.flatten_nil] at hq; exact List.not_mem_nil hq` 两步
    确定型。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:14211-:14428，十六
  落件 + 两记档不落）：

  §1 list_update/mapAt 章首：`size_list_update` :14211-:14217 ↦
    sizeListUpdate（List.set 载体 + `List.length_set` 一发）；`
    size_replacefacesAt` :14220-:14228 ↦ sizeReplacefacesAt
    （replacefacesAt 定义形 defeq 直投 length_mapAt）。
  §2 vertices_set2 章：`vertices_set2_countVertices` :14231-:14237 ↦
    verticesSet2CountVertices（新 def VerticesSet2Spine + Iff.rfl）。
  §3 replace/cat 家族：`replace_id` :14240-:14247 ↦ replaceId（归纳
    两支 + if_neg，批 58 replaceSpineMiss 公开化同证）；`cat_to_fst`
    :14250-:14280 ↦ catToFst（cons 归纳两分——HOL
    indexl/take/drop 六步机制面在 Lean 面收缩为 cons 归纳四支，存在
    证人构造性等价，机制简化记档零收窄）；`replace_hd` :14283-:14288 ↦
    replaceHd（show 换面 + if_pos rfl）；`replace_cat2` :14291-:14296 ↦
    replaceCat2（cons 归纳 + append cons defeq 墙走 show）；`cat_tl`
    :14299-:14304 ↦ catTl（cons 支纯 defeq rfl）。
  §4 尺寸面：`map_size_list_of_faces` :14321-:14330 ↦
    mapSizeListOfFaces（listOfFaces unfold + map_map 单层 +
    map_congr_left 回喂 la7_length_listPairs）；`foldr_size_max`
    :14333-:14340 ↦ foldrSizeMax（foldr/map cons defeq show +
    le_max 双支）。
  §5 iso_list 尾章：`iso_list_size` :14351-:14360 ↦ isoListSize
    （hL 方程 + map_map + map_congr_left + length_map 回喂）；
    `iso_list_snd` :14363-:14376 ↦ isoListSnd（isoListSpineSym 空表
    真空前提 + isoListSpineTrans 双向）；`is_restricted_all_uniq`
    :14379-:14387 ↦ isRestrictedAllUniq（IsRestricted.simple 投影 +
    simpleHypermapUniq 一发）；`isop_list_iso_list` :14390-:14395 ↦
    isopListIsoList（IsoListSpine ∃-折叠定义形 Iff.rfl）。
  §6 收官两件：`map_id_eq` :14398-:14411 ↦ mapIdEq（cons 归纳 +
    cons.injEq，g 自由变元显式化记账）；`uniq_flatten_all_uniq`
    :14414-:14422 ↦ uniqFlattenAllUniq（批 5 uniqFlattenUniq :3872
    同语句别名件——PEUTLZH 体例）。
  §7 记档不落两枚：`mem_faces_fgraph` :14343-:14349（批 2 fgraphFaces
    在册命中，批 58 §6 既记，本批收口段内再记）；`uniq_flatten_all_uniq`
    的 :3872 同型件 uniqFlattenUniq 在册命中（本批按别名落件，双保险
    记账）。

  诚实记账：十六件落件全真证（sizeListUpdate/sizeReplacefacesAt/
  verticesSet2CountVertices/replaceId/catToFst/replaceHd/replaceCat2/
  catTl/mapSizeListOfFaces/foldrSizeMax/isoListSize/isoListSnd/
  isRestrictedAllUniq/isopListIsoList/mapIdEq/uniqFlattenAllUniq）+
  新 def 一枚（VerticesSet2Spine，定义形），零 sorry、零止损件、零
  记账债。axiom 审计：十六探针全标准三内零 sorryAx——无公理六件
  （verticesSet2CountVertices/replaceId/replaceHd/replaceCat2/catTl/
  isopListIsoList）、[propext] 三件（sizeListUpdate/foldrSizeMax/
  mapIdEq）、[propext, Quot.sound] 三件（mapSizeListOfFaces/
  isoListSize/uniqFlattenAllUniq）、标准三三件（catToFst/isoListSnd/
  isRestrictedAllUniq）（详见尾注锚）。
  范围决策：批 59 射程 = :14211-:14428 全段，tame_list.hl 至此全本
  收官（B1 线里程碑）；零既有文件触碰、零 git 写操作。
  下一章接续点：tame/ 目录 64 文件待勘域（reduction1.hl :1 起 4976
  行为 B1 线处方候选——批 56 is_restricted 章、批 49 normal_list 章
  已越章预收其部分件，开工先查在册命中面），由编排者裁定批次表。
-/

import Kepler.Text.TameSpine.TameList58

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl la7_length_listPairs)

/-! ### §1 list_update/mapAt 章首（tame_list.hl:14211/:14220） -/

/-- **HOL `size_list_update`**（tame_list.hl:14211-:14217
`!xs i v. sizel (list_update xs i v) = sizel xs`）。
载体对拍：list_update（tame_defs2.hl:194-:197）↦ `List.set`（cons 方程
`i=0 → v::xs / n+1 → x::xs.set n v` 与 HOL else 支 nat 截断减法逐点
一致），sizel ↦ `List.length`——核心 `List.length_set` 一发。 -/
theorem sizeListUpdate {α : Type*} (xs : List α) (i : Nat) (v : α) :
    (xs.set i v).length = xs.length :=
  List.length_set

/-- **HOL `size_replacefacesAt`**（tame_list.hl:14220-:14228
`!ns f fs Fs. sizel (replacefacesAt ns f fs Fs) = sizel Fs`）。
replacefacesAt（tame_defs2.hl:278-:279）↦ `Kepler.Graphs.replacefacesAt`
（FaceDivision.lean:17 Face 特化形，= `mapAt ns (replace f fs) F` 定义
形）——在册 `Kepler.Graphs.length_mapAt`（ListAuxLemmas.lean:814）defeq
直投，HOL 的 ns 归纳/COND 分流/size_list_update 回喂三步在 Lean 面由
在册泛件一次吸收（机制简化记档零收窄）。 -/
theorem sizeReplacefacesAt (ns : List Nat) (f : Kepler.Graphs.Face)
    (fs : List Kepler.Graphs.Face) (F : List (List Kepler.Graphs.Face)) :
    (Kepler.Graphs.replacefacesAt ns f fs F).length = F.length :=
  Kepler.Graphs.length_mapAt

/-! ### §2 vertices_set2 章（tame_list.hl:14231） -/

/-- HOL `vertices_set2`（tame_defs.hl:392-:394
`vertices_set2 g = set_of_list (vertices_graph g)`，vertices_graph
（tame_defs.hl:389）= `upt 0 (countVertices g)`）逐句镜像——iota 0 n
= `[0,…,n-1]`、set_of_list 集合化定义形 collapse 为 `{v | v <
g.countVertices}`（Kepler.Graphs.Graph.vertices = List.range
countVertices 同层；HOL 证体 REWRITE[vertices_set2;IN_SET_OF_LIST;
vertices_graph;upt0;Seq.mem_iota] + ARITH_TAC 即此面）。 -/
def VerticesSet2Spine (g : Kepler.Graphs.Graph) : Set ℕ :=
  {v : ℕ | v < g.countVertices}

/-- **HOL `vertices_set2_countVertices`**（tame_list.hl:14231-:14237
`!g v. v < countVertices g <=> v IN vertices_set2 g`）——上注 def 形下
即定义性 Iff.rfl（HOL ARITH_TAC 同面）。 -/
theorem verticesSet2CountVertices (g : Kepler.Graphs.Graph) (v : ℕ) :
    v < g.countVertices ↔ v ∈ VerticesSet2Spine g :=
  Iff.rfl

/-! ### §3 replace/cat 家族（tame_list.hl:14240/:14250/:14283/:14291/:14299） -/

/-- **HOL `replace_id`**（tame_list.hl:14240-:14247
`!f a b. ~MEM a f ==> replace a b f = f`）。
replace ↦ replaceSpine（批 17 泛 α 形；b 即替换表——新雷区一）；f 归纳
两支——nil 支定义形 rfl，cons 支 replaceSpine 方程 + if_neg（z ≠ a 槽
由 a ∉ z::zs 换装）+ 归纳假设回喂。批 58 私件 replaceSpineMiss（x 不
在表 replace 恒等）为同型件，私件不跨模块，本件按公开件同证重推导
（批 7→8 惯例）。 -/
theorem replaceId {α : Type*} [DecidableEq α] (a : α) (b : List α)
    (f : List α) (h : a ∉ f) : replaceSpine a b f = f := by
  induction f with
  | nil => rfl
  | cons z zs ih =>
    have hz : ¬(z = a) := by
      intro hza
      rw [hza] at h
      exact h (List.mem_cons_self ..)
    rw [replaceSpine, if_neg hz, ih (fun hx => h (List.mem_cons_of_mem _ hx))]

/-- **HOL `cat_to_fst`**（tame_list.hl:14250-:14280
`!(x:A) s. MEM x s ==> (?a b. s = cat a b /\ x = HD b /\ ~(MEM x a)
/\ ~(b = []))`）。cat/HD/MEM ↦ `++`/`head!`/`∈`。证体：cons 归纳两分
（x 命中首元支证人 `⟨[], x::ys⟩`、未命中支递归证人首元扩装）——HOL
indexl/cat_take_drop/index_cat/index_mem/size_drop/size_takel/index0
六步机制面在 Lean 面收缩为 cons 归纳两支，存在证人构造性等价，机制
简化记档零收窄（b ≠ [] 合取支封死 head! 空表 junk 面；`[Inhabited α]`
实例参随 head! 载体，新雷区二）。 -/
theorem catToFst {α : Type*} [Inhabited α] {s : List α} (x : α) (h : x ∈ s) :
    ∃ a b, s = a ++ b ∧ x = b.head! ∧ x ∉ a ∧ b ≠ [] := by
  induction s with
  | nil => exact absurd h (by simp)
  | cons y ys ih =>
    by_cases hxy : x = y
    · subst hxy
      exact ⟨[], x :: ys, rfl, rfl, by simp, List.cons_ne_nil x ys⟩
    · have hin : x ∈ ys := by
        rcases List.mem_cons.mp h with heq | hm
        · exact absurd heq hxy
        · exact hm
      obtain ⟨a, b, hsb, hxb, hxa, hbne⟩ := ih hin
      refine ⟨y :: a, b, by rw [List.cons_append, hsb], hxb, ?_, hbne⟩
      intro hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · exact hxy heq
      · exact hxa hmem'

/-- **HOL `replace_hd`**（tame_list.hl:14283-:14288
`!b f. ~(b = []) ==> replace (HD b) f b = cat f (TL b)`）。
b cases 两支——nil 支矛盾封死（HD/TL junk 面由非空前提排除），cons
支 show 换面（head!/tail 定义形）+ replaceSpine 方程 + if_pos rfl
（HOL 下位 REWRITE[HD;TL;replace] + lower_case 的 APPEND_cat 面 =
Lean `++` 统一记法，机制面 collapse 记档）；`[Inhabited α]` 实例参
随 head! 载体（新雷区二，memHd 体例）。 -/
theorem replaceHd {α : Type*} [DecidableEq α] [Inhabited α] (f : List α)
    (b : List α) (h : b ≠ []) : replaceSpine b.head! f b = f ++ b.tail := by
  cases b with
  | nil => exact absurd rfl h
  | cons y ys =>
    show replaceSpine y f (y :: ys) = f ++ ys
    rw [replaceSpine, if_pos rfl]

/-- **HOL `replace_cat2`**（tame_list.hl:14291-:14296
`!u x f v. ~(MEM x u) ==> replace x f (cat u v) = cat u
(replace x f v)`）。u 归纳两支——nil 支双翼 `[] ++ _` 定义形 rfl；
cons 支 show 换面（append cons defeq 墙，批 58 雷区同源）+
replaceSpine 方程 + if_neg（y ≠ x 槽换装）+ 归纳假设回喂 + cons_append
收口。 -/
theorem replaceCat2 {α : Type*} [DecidableEq α] (x : α) (f : List α)
    (v u : List α) (h : x ∉ u) :
    replaceSpine x f (u ++ v) = u ++ replaceSpine x f v := by
  induction u with
  | nil => rfl
  | cons y ys ih =>
    have h1 : ¬(y = x) := by
      intro hxx
      rw [hxx] at h
      exact h (List.mem_cons_self ..)
    have h2 : x ∉ ys := fun hx => h (List.mem_cons_of_mem _ hx)
    show replaceSpine x f (y :: (ys ++ v)) = (y :: ys) ++ replaceSpine x f v
    rw [replaceSpine, if_neg h1, ih h2, List.cons_append]

/-- **HOL `cat_tl`**（tame_list.hl:14299-:14304
`!a b. ~(a=[]) ==> TL (cat a b) = cat (TL a) b`）——cons 支双翼纯
defeq（append/tail 的 cons iota 归约）rfl 一发；nil 支矛盾封死。 -/
theorem catTl {α : Type*} (a b : List α) (h : a ≠ []) :
    (a ++ b).tail = a.tail ++ b := by
  cases a with
  | nil => exact absurd rfl h
  | cons y ys => rfl

/-! ### §4 尺寸面（tame_list.hl:14321/:14333；:14343 记档不落） -/

/-- **HOL `map_size_list_of_faces`**（tame_list.hl:14321-:14330
`!L. MAP sizel (list_of_faces L) = MAP sizel L`）。
list_of_faces（list_hypermap-compiled.hl:26 `MAP list_pairs L`）↦ 批 31
`listOfFaces`（逐字同形）；HOL GSYM MAP_o + MAP_EQ + size_list_pairs
三步在 Lean 面 = map_map 单层 + map_congr_left 回喂
`la7_length_listPairs`（TameLp 泛 α 形，批 14 头注预记命中）。 -/
theorem mapSizeListOfFaces (L : fgraph ℕ) :
    (listOfFaces L).map List.length = L.map List.length := by
  rw [listOfFaces, List.map_map]
  exact List.map_congr_left (fun p _ => la7_length_listPairs p)

/-- **HOL `foldr_size_max`**（tame_list.hl:14333-:14340
`!xs x. MEM x xs ==> sizel x <= foldr maxn 0 (MAP sizel xs)`）。
xs cases 两支——nil 支 MEM 矛盾封死；cons 支 foldr/map cons defeq
show 换面 + le_max 双支（x = y 走 le_max_left、x ∈ ys 走 le_trans +
le_max_right，HOL Ssrnat.leq_maxr + MESON 同构）。 -/
theorem foldrSizeMax {α : Type*} {xs : List (List α)} {x : List α}
    (h : x ∈ xs) :
    List.length x ≤ (xs.map List.length).foldr max 0 := by
  cases xs with
  | nil => cases h
  | cons y ys =>
    show List.length x ≤ max (List.length y) ((ys.map List.length).foldr max 0)
    rcases List.mem_cons.mp h with heq | h'
    · subst heq
      exact le_max_left _ _
    · exact le_trans (foldrSizeMax h') (le_max_right _ _)

/-! 记档不落：HOL `mem_faces_fgraph`（tame_list.hl:14343-:14349
`!f g. MEM f (faces g) ==> MEM (FST f) (fgraph g)`）——批 2
`fgraphFaces`（TameList2.lean:97，:184 fgraph_Faces 面）在册命中，批 58
§6 尾注既记（faces/Faces = set_of_list 面两前提 collapse）；本段
:14211-:14428 收口段内含此锚，再记一次免漏账。 -/

/-! ### §5 iso_list 尾章（tame_list.hl:14351/:14363/:14379/:14390） -/

/-- **HOL `iso_list_size`**（tame_list.hl:14351-:14360
`!L L'. iso_list (L',[]) (L,[]) ==> MAP sizel L' = MAP sizel L`）。
方向对拍（批 58 预记命中）：`IsoListSpine L₁ L₂` 第二参数是像——HOL
`iso_list (L',[]) (L,[])` ↦ `IsoListSpine L' L [] []`，零换向。证体：
φ 方程（L = MAP MAP phi L'）重写 + map_map 单层 + map_congr_left 回喂
`List.length_map`（HOL Seq.size_map + MAP_EQ + lower_case/allP 机制
面在 Lean 面收缩两发，机制简化记档零收窄）。 -/
theorem isoListSize {L L' : fgraph ℕ} {N N' : List (List (ℕ × ℕ))}
    (h : IsoListSpine L' L N N') :
    L'.map List.length = L.map List.length := by
  obtain ⟨phi, -, hL, -⟩ := h
  rw [hL, List.map_map]
  refine List.map_congr_left (fun a _ => ?_)
  show List.length a = (a.map phi).length
  rw [List.length_map]

/-- **HOL `iso_list_snd`**（tame_list.hl:14363-:14376
`!L L' L''. iso_list (L,[]) (L',[]) ==> (iso_list (L,[]) (L'',[])
<=> iso_list (L',[]) (L'',[]))`）。链件全在册：`iso_list_sym_nil`
（:3701）面 = 批 4 `isoListSpineSym` 空表真空前提形（N.flatten = []
双前提恒假——免批 5 isoListSpineSymNil 形的 GoodList 前提，HOL 原句
无此前提，语义零收窄）；`iso_list_trans`（more_tame_concl.hl:153）↦
批 4 `isoListSpineTrans` 直投（EQ_EXPAND 双向 = constructor 双支）。 -/
theorem isoListSnd {L L' L'' : fgraph ℕ} {N'' : List (List (ℕ × ℕ))}
    (h : IsoListSpine L L' [] []) :
    IsoListSpine L L'' [] N'' ↔ IsoListSpine L' L'' [] N'' := by
  have hvac : ∀ q : ℕ × ℕ, ¬(q ∈ ([] : List (List (ℕ × ℕ))).flatten) := by
    intro q hq
    rw [List.flatten_nil] at hq
    exact List.not_mem_nil hq
  have hsym : IsoListSpine L' L [] [] :=
    isoListSpineSym h (fun p hp => absurd hp (hvac p)) (fun p hp => absurd hp (hvac p))
  constructor
  · intro h2
    exact isoListSpineTrans hsym h2
  · intro h2
    exact isoListSpineTrans h h2

/-- **HOL `is_restricted_all_uniq`**（tame_list.hl:14379-:14387
`!L. good_list L /\ good_list_nodes L /\ is_restricted
(hypermap_of_list L) ==> all uniq L`）。链 = `Hypermap.IsRestricted`
第五合取项 `.simple` 直取（hypermap.hl:11174 定义形）+ 批 14
`simpleHypermapUniq`（:9254 在册）mp 一发（HOL MESON
[simple_hypermap_uniq] 同构）。 -/
theorem isRestrictedAllUniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted) :
    ∀ l ∈ L, l.Nodup :=
  (simpleHypermapUniq L hL hgn).mp hres.simple

/-- **HOL `isop_list_iso_list`**（tame_list.hl:14390-:14395
`!L N L' N'. (?p. isop_list p (L,N) (L',N')) <=> iso_list (L,N)
(L',N')`）——IsoListSpine 的 ∃-折叠定义形（TameList1.lean:67），
定义性 Iff.rfl（批 58 planeGraphExP 同体例）。 -/
theorem isopListIsoList {L L' : fgraph ℕ} {N N' : List (List (ℕ × ℕ))} :
    (∃ phi, IsopListSpine phi L L' N N') ↔ IsoListSpine L L' N N' :=
  Iff.rfl

/-! ### §6 收官两件（tame_list.hl:14398/:14414） -/

/-- **HOL `map_id_eq`**（tame_list.hl:14398-:14411
`!f xs. MAP f xs = MAP g xs <=> (all (\x. f x = g x) xs)`）。
记账：HOL 语句 g 为自由变元（隐式全称），Lean 面显式入 binder。
l 归纳两支——nil 支双向（mem 矛盾 / 定义形 rfl）；cons 支 show 换面
（map cons iota）+ `List.cons.injEq` 拆条 + mem_cons 双支回喂（HOL
EQ_EXPAND + MAP/all cons 展开 + CONS_11 + MESON 同构）。 -/
theorem mapIdEq {α : Type*} {β : Type*} (f g : α → β) (l : List α) :
    l.map f = l.map g ↔ ∀ a ∈ l, f a = g a := by
  induction l with
  | nil =>
    constructor
    · intro _ a ha
      exact absurd ha (by simp)
    · intro _; rfl
  | cons y ys ih =>
    show f y :: ys.map f = g y :: ys.map g ↔ ∀ a ∈ y :: ys, f a = g a
    rw [List.cons.injEq]
    constructor
    · rintro ⟨h1, h2⟩ a ha
      rcases List.mem_cons.mp ha with heq | ha
      · rw [heq]
        exact h1
      · exact ih.mp h2 a ha
    · intro hall
      exact ⟨hall y (List.mem_cons_self ..),
        ih.mpr fun a ha => hall a (List.mem_cons_of_mem _ ha)⟩

/-- **HOL `uniq_flatten_all_uniq`**（tame_list.hl:14414-:14422
`!s. uniq (flatten s) ==> all uniq s`）——批 5 `uniqFlattenUniq`
（TameList5.lean:319，tame_list.hl:3872 `uniq_flatten_uniq` 的
∀/→ 平铺形）同语句别名件（PEUTLZH 体例，供下游按 HOL 名检索；
flatten/all 载体约定见批 5 头注）。 -/
theorem uniqFlattenAllUniq {α : Type*} (s : List (List α))
    (h : s.flatten.Nodup) : ∀ l ∈ s, l.Nodup :=
  uniqFlattenUniq s h

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；十六件正文全绿零 sorryAx——
#print axioms Kepler.Text.TameSpine.sizeListUpdate
#print axioms Kepler.Text.TameSpine.sizeReplacefacesAt
#print axioms Kepler.Text.TameSpine.verticesSet2CountVertices
#print axioms Kepler.Text.TameSpine.replaceId
#print axioms Kepler.Text.TameSpine.catToFst
#print axioms Kepler.Text.TameSpine.replaceHd
#print axioms Kepler.Text.TameSpine.replaceCat2
#print axioms Kepler.Text.TameSpine.catTl
#print axioms Kepler.Text.TameSpine.mapSizeListOfFaces
#print axioms Kepler.Text.TameSpine.foldrSizeMax
#print axioms Kepler.Text.TameSpine.isoListSize
#print axioms Kepler.Text.TameSpine.isoListSnd
#print axioms Kepler.Text.TameSpine.isRestrictedAllUniq
#print axioms Kepler.Text.TameSpine.isopListIsoList
#print axioms Kepler.Text.TameSpine.mapIdEq
#print axioms Kepler.Text.TameSpine.uniqFlattenAllUniq
-/
