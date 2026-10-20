/-
  Kepler.Text.TameSpine.TameList58 — B1 Tame_list 地基批 58：
  list_pairs_core 开章（normal_list/core/parts 新章）+ planegraph/minimal/
  flag/makeFaceFinal 簇收口（tamespine-port-plan §4 批次表 B1 行；接续
  批 57 = TameList57.lean，批 57 终点 = HOL :14054（size2_cons）；本批
  起点 = HOL :14057 `list_pairs_core`。行号均按主仓 reference/flyspeck
  （commit 1ce0353）实测；批 57 尾注预记 :14057 与实测一致，零偏移。

  载体侦察裁定（批 57 尾注预记面的对拍结论）：

  - **core 载体既档**（批 57 预记「开工先核」命中）：HOL `core`
    （tame_defs2.hl:129-:130 `core L r = MAP (FST o HD) (parts L r)`）
    ↦ 批 7 `coreSpine`（TameList7.lean:466，`(partsSpine L r).map
    (fun a => a.head!.1)`）——show 定义形换形一发。
  - **parts_list_pairs 既档**（批 57 预记命中）：HOL :6822-:6884
    `parts_list_pairs` ↦ 批 10 `partsListPairs`（TameList10.lean:553，
    语句含五前提全量形）——本批主件证体即一次直投（HOL 证体
    REWRITE[core] + INTRO_TAC parts_list_pairs + SUBST1 o GSYM +
    AP_TERM/AP_THM + o_THM/FUN_EQ_THM 五步在 Lean 面收缩为 show 换形 +
    exact 一发：coreSpine 定义形与 partsListPairs 的 MAP 形 defeq，
    机制简化记档非语义损失）。
  - **planegraphP 载体分歧记档（新章裁定）**：Kepler.Graphs.PlaneGraphsP
    （Plane1.lean:27，AFP Flyspeck-Tame 移植形）多一 `∧ g.final` 合取；
    HOL `planegraphP`（tame_defs2.hl:437-:439）无此项——HOL 形与 AFP
    形语义分歧，本 lane 按 HOL 镜像另立 `PlaneGraphPSpine`/
    `PlaneGraphSpine` 两 def（Seed/next_plane/RTranCl 全在册直投），
    planegraph_P 即定义性 rfl；AFP 形不消费（分歧记档非止损）。
  - **minimal 簇载体全在册**：mem_minimal_el（tame_list.hl:803）↦ 批 2
    `memMinimalEl`（TameList2.lean:273，本体 Kepler.Graphs.minimal_in_set
    Isabelle 同源）；mem_minimalFace_nonFinals（:13196）↦ 批 52
    `memMinimalFaceNonFinals`（TameList52.lean:139）；minimalVertex/
    minimalFace ↦ Kepler.Graphs.Plane1 同名（Plane1.lean:15/:12）。
  - **flag 簇载体在册**：flag_list/s_flag_list（tame_defs2.hl:512/:495）
    ↦ 批 13 `FlagListSpine`/`SFlagListSpine`（TameList13.lean:239/:252）。
  - **makeFaceFinal 簇全在册**：makeFaceFinal/makeFaceFinalFaceList ↦
    Kepler.Graphs.FaceDivision（AFP 层，Graph 结构字段一一对拍——三件
    rfl 零镜像）；setFinal ↦ Kepler.Graphs.setFinal（Graph.lean:56，
    批 2 setFinalAlt 同层，批 56 sndSetFinal 对偶件 fst_setFinal 本批落）。
  - **replace 载体在册**：HOL replace（tame_defs.hl:317-:320）↦ 批 17
    `replaceSpine`（TameList17.lean:75）；filter 面按批 56 filterReplace
    体例（decide 装箱 + filter_append/filter_cons_of_pos/neg）。
  - **fgraph_Faces/faces 双面记档**：HOL :184 `fgraph_Faces`（`Faces g =
    set_of_list (faces g)` 面，FACES tame_defs.hl:373）批 2 `fgraphFaces`
    （TameList2.lean:97）在册；:14343 `mem_faces_fgraph`（MEM 面同结
    论）在 Lean 折算面逐字同语句（两前提面 collapse 到 `F ∈ g.faces`）
    ——记档不落。

  新雷区（本批实测记档）：
  - **rw [def] 的 cons-字面量匹配墙 + replaceSpine 尾段保留语义**：
    replaceSpine 方程按 cons 字面量匹配（`replaceSpine ?x ?ys
    (?z :: ?zs)`），`replaceSpine f [S] zs`（zs 自由变元）与
    `replaceSpine f [S] (filter p (z :: zs))`（filter 应用非 reducible
    可见 cons）都不进第一发的实例——每发 rw 只吃首个字面量 cons 支路，
    右翼 filter 包裹支路须待 filter_cons 发后再发；又 replaceSpine 命中
    支为 `ys ++ zs` 尾段保留（非递归），z = f 分支归纳假设零消费（两翼
    cons 归一即 rfl），ih 只在 z ≠ f 递归支消费——filter_append 双翼
    归一即可收口，勿画蛇添足补 ih。
  - **named-arg p 钉参须全类型注记**：`List.filter_cons_of_pos
    (p := fun F => decide (v ∈ F.vertices)) h` 裸写时 named-arg 先于
    α 实例化，F 类型悬空致 `.vertices` 投影解析失败（Invalid field
    notation 报到 F 头上），须 `(p := fun (F : Kepler.Graphs.Face) =>
    ...)` 全注记；钉参后 h 槽按 β-defeq 直投。附带：Iff 结论 rfl 不进
    （Not a definitional equality: conclusion should be an equality），
    走 Iff.rfl（planeGraphExP 槽）。
  - **P 假支 replace-miss 槽私件补位**：mem_fst_setFinal z = f / P f 假
    支收口面 `filter P zs = replaceSpine f [S] (filter P zs)` 非 rfl 非
    ih（尾段保留语义下 ih 只覆盖递归支）——实为 f 被 filter P 尽出后
    replace 恒等，私件 replaceSpineMiss（x 不在表 replace 恒等，三行
    归纳）补位；HOL ASM_SIMP_TAC[filter_non_mem_setFinal] 的机制面不可
    直译（其收口依赖 set_of_list 面假设重写），机制差异记档非语义损失。
  - **非 subst 的分支证人对称桥**：z = f 分支不 subst（方向不可预期）
    ——三处 ite/filter 槽的证人各按原形立：`hPz : decide (v ∈ z.vertices)
    = true := by rw [hz]; exact hP`（rw 换装）与 `hS : decide (v ∈
    (setFinal f).vertices) = true := hP`（setFinal 字段面 defeq 直投）
    并存；defeq 直投只对「函数应用套字段投影」面成立，跨 hz 的两变元
    面必须走 rw 换装，不可混用。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:14057-:14203 + :14307，
  十三件）：

  §1 主件：`list_pairs_core` :14057-:14073 ↦ listPairsCore（真证；coreSpine
    show 定义形 + partsListPairs 批 10 直投，HOL 五步机制收缩记档）。
  §2 planegraph/minimal 簇：`planegraph_P` :14077-:14084 ↦ planeGraphExP
    （真证；新 def PlaneGraphPSpine/PlaneGraphSpine 定义性 rfl，载体
    分歧记档）；`mem_minimalVertex` :14085-:14092 ↦ memMinimalVertex
    （memMinimalEl 直投）；`minimalFace_face` :14094-:14105 ↦
    minimalFaceFace（memMinimalFaceNonFinals + mem_filter 链）。
  §3 flag 簇：`flag_list_s_flag_list` :14107-:14120 ↦ flagListSFlagList
    （首合取 defeq 直投 + 尾合取 mem_cat 取右支——HOL DISJ2_TAC 同构）。
  §4 nonFinals/makeFaceFinal/setFinal 簇：`nonFinals_fgraph` :14122-:14132
    ↦ nonFinalsFgraph（mem_of_mem_filter + fgraphFaces 两步）；`
    faceListAt_makeFaceFinal` :14134-:14144 ↦ faceListAtMakeFaceFinal
    （rfl——HOL ETA_AX 面 Lean 原生 eta）；`faces_makeFaceFinal`
    :14146-:14151 ↦ facesMakeFaceFinal（rfl）；`fst_setFinal` :14154-:14159
    ↦ setFinalFst（rfl——名撞记档：批 2 fstSetFinal 系 tame_list.hl:207
    `MAP FST (replace f [setFinal f] vs) = MAP FST vs` 的 replace 面，
    本件换名）；`filter_non_mem_setFinal` :14162-:14177 ↦
    filterNonMemSetFinal（vs 归纳两支 + 新雷区一）；`mem_fst_setFinal`
    :14179-:14201 ↦ memFstSetFinal（vs 归纳 + z=f/≠f × P 真/假 四分流，
    新雷区一三）；`countVertices_makeFaceFinal` :14203-:14208 ↦
    countVerticesMakeFaceFinal（rfl）。
  §5 越章随收：`mem_minimalFace_fgraph` :14307-:14317 ↦
    memMinimalFaceFgraph（minimalFaceFace + fgraphFaces 两步链）。
  §6 记档不落一件：`mem_faces_fgraph` :14343（fgraphFaces 批 2 在册
    命中，faces/Faces 双面 collapse 记档如上）。

  诚实记账：十三件落件全真证（listPairsCore/planeGraphExP/
  memMinimalVertex/minimalFaceFace/flagListSFlagList/nonFinalsFgraph/
  faceListAtMakeFaceFinal/facesMakeFaceFinal/setFinalFst/
  filterNonMemSetFinal/memFstSetFinal/countVerticesMakeFaceFinal/
  memMinimalFaceFgraph）+ 私件 replaceSpineMiss（memFstSetFinal 假支
  槽），零 sorry、零止损件、零记账债；新 def 两枚
  （PlaneGraphPSpine/PlaneGraphSpine，均定义形）。axiom 审计：十四探针
  （十三正文 + 私件模块内插）全标准三内零 sorryAx（[propext,
  Classical.choice, Quot.sound] 面，五件无公理：四 rfl 件 +
  replaceSpineMiss）。
  范围决策：批 58 射程收口至 :14208（core/parts 章首件 + minimal/flag/
  makeFaceFinal 簇 + :14307 越章随收）——自然边界：下一件 :14211
  `size_list_update` 起为 list_update/mapAt 载体新章（含 replace 家族
  :14240-:14299 与 cat_to_fst :14250 大件、map_size_list_of_faces
  :14321、foldr_size_max :14333、iso_list_size :14351 至文件末 :14428）。
  红线遵守：零既有文件触碰、零 git 写操作。
  批 59 接续点：HOL :14211 `size_list_update`（`!xs i v. sizel
  (list_update xs i v) = sizel xs`——list_update（tame_defs2.hl:194-:197）
  载体不在册开工先核，Lean 面 List.set 候选对拍）；其后 :14218
  size_replacefacesAt（mapAt/replacefacesAt ↦ Kepler.Graphs.ListAux:61/
  FaceDivision:17 既档）、:14226 vertices_set2_countVertices、:14240
  replace_id、:14250 cat_to_fst（indexl/take/drop 机制大件）、:14283
  replace_hd、:14291 replace_cat2、:14299 cat_tl、:14321
  map_size_list_of_faces（list_of_faces 批 31 + size_list_pairs 载体
  先核）、:14333 foldr_size_max、:14351 iso_list_size（IsoListSpine 批 1
  方向对拍先核）。
-/

import Kepler.Text.TameSpine.TameList56

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs GoodList)
open Kepler.Graphs (fgraph nonFinals minimalFace minimalVertex setFinal
  makeFaceFinal makeFaceFinalFaceList next_plane Seed RTranCl)
open Kepler.Text.TameLp (hypermapOfList)

/-! ### §1 core/parts 章首件（tame_list.hl:14057） -/

/-- **HOL `list_pairs_core`**（tame_list.hl:14057-:14073
`!L N r. normal_list L N /\ is_edge_nondegenerate (hypermap_of_list L) /\
good_list L /\ MEM r N /\ all uniq L ==> list_pairs (core L r) =
MAP LAST (parts L r)`）。
证体：core ↦ coreSpine（批 7，tame_defs2.hl:130 定义形）show 换形；
HOL REWRITE[core] + INTRO_TAC parts_list_pairs + SUBST1 o GSYM +
AP_TERM/AP_THM + o_THM/FUN_EQ_THM 五步在 Lean 面收缩为 show + exact
一发（coreSpine 定义形与批 10 partsListPairs 的 MAP 形 defeq，机制
简化记档非语义损失）。 -/
theorem listPairsCore (L : fgraph ℕ) (hL : GoodList L) {N : List (List (ℕ × ℕ))}
    (hn : NormalListSpine hL N) (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {r : List (ℕ × ℕ)} (hr : r ∈ N) :
    listPairs (coreSpine L r) = (partsSpine L r).map (fun q => q.getLast!) := by
  show listPairs ((partsSpine L r).map (fun a => a.head!.1)) = _
  exact partsListPairs L hL hn hnedg hunL hr

/-! ### §2 planegraph/minimal 簇（tame_list.hl:14077/:14085/:14094） -/

/-- HOL `planegraphP`（tame_defs2.hl:437-:439
`planegraphP p g = ((Seed p,g) IN RTranCl (next_plane p))`）逐句镜像
（Seed ↦ Kepler.Graphs.Seed、next_plane ↦ Kepler.Graphs.next_plane、
RTranCl ↦ Kepler.Graphs.RTranCl 全在册）。载体分歧记档：AFP 移植形
Kepler.Graphs.PlaneGraphsP（Plane1.lean:27）多一 `∧ g.final` 合取，
HOL 形无——按 HOL 镜像另立本 def（语义零收窄）。 -/
def PlaneGraphPSpine (p : ℕ) (g : Kepler.Graphs.Graph) : Prop :=
  RTranCl (next_plane p) (Seed p) g

/-- HOL `planegraph`（tame_defs2.hl:427-:431
`planegraph g = (?p. (Seed p,g) IN RTranCl (next_plane p))`）逐句镜像
（载体分歧记档同上：Kepler.Graphs.PlaneGraphs 为 AFP 形）。 -/
def PlaneGraphSpine (g : Kepler.Graphs.Graph) : Prop :=
  ∃ p, PlaneGraphPSpine p g

/-- **HOL `planegraph_P`**（tame_list.hl:14077-:14084
`!g. planegraph g <=> (?p. planegraphP p g)`）——HOL
REWRITE_TAC[planegraph;planegraphP] 定义性一发，Lean 面即定义形 rfl。 -/
theorem planeGraphExP (g : Kepler.Graphs.Graph) :
    PlaneGraphSpine g ↔ ∃ p, PlaneGraphPSpine p g := Iff.rfl

/-- **HOL `mem_minimalVertex`**（tame_list.hl:14085-:14092
`!g f. ~(FST f=[]) ==> MEM (minimalVertex g f) (FST f)`）。
minimalVertex ↦ Kepler.Graphs.minimalVertex（Plane1.lean:15，= minimal
(height g) f.vertices 定义形）；槽 = memMinimalEl（批 2，tame_list.hl:803
mem_minimal_el 在册）直投。 -/
theorem memMinimalVertex (g : Kepler.Graphs.Graph) (f : Kepler.Graphs.Face)
    (h : f.vertices ≠ []) : minimalVertex g f ∈ f.vertices :=
  memMinimalEl (Kepler.Graphs.height g) h

/-- **HOL `minimalFace_face`**（tame_list.hl:14094-:14105
`!g. ~finalGraph g ==> MEM (minimalFace (nonFinals g)) (faces g)`）。
~finalGraph ↦ Graph.final g = false（批 56 finalGraphFilter 同层）；链
= memMinimalFaceNonFinals（批 52）+ nonFinals filter 面出
List.mem_filter（HOL mem_minimalFace_nonFinals 槽 + MEM_FILTER 两步）。 -/
theorem minimalFaceFace (g : Kepler.Graphs.Graph)
    (hf : Kepler.Graphs.Graph.final g = false) :
    minimalFace (nonFinals g) ∈ g.faces := by
  have hne : nonFinals g ≠ [] := by
    intro hnil
    have h2 : (nonFinals g).isEmpty = false := hf
    rw [hnil] at h2
    simp at h2
  have hm := memMinimalFaceNonFinals g hne
  rw [nonFinals, List.mem_filter] at hm
  exact hm.1

/-! ### §3 flag 簇（tame_list.hl:14107） -/

/-- **HOL `flag_list_s_flag_list`**（tame_list.hl:14107-:14120
`!L N r x. flag_list L N ==> s_flag_list L N r x`）。
flag_list/s_flag_list ↦ 批 13 FlagListSpine/SFlagListSpine；首合取
两 def 同形 defeq 直投；尾合取：Seq.mem_cat 面 ↦ List.mem_append_right
取右支（HOL DISJ2_TAC + flag_list 尾合取 MATCH_MP 同构，s_list 前件
`~MEM y (s_list L r x)` 槽闲置 `_`）。 -/
theorem flagListSFlagList (L : fgraph ℕ) {N : List (List (ℕ × ℕ))}
    (hf : FlagListSpine L N) (r : List (ℕ × ℕ)) (x : ℕ × ℕ) :
    SFlagListSpine L N r x := by
  obtain ⟨hA, hB⟩ := hf
  refine ⟨hA, ?_⟩
  intro r' p y hy hp hrn hfin _
  exact List.mem_append_right _ (hB r' p y hy hp hrn hfin)

/-! ### §4 nonFinals/makeFaceFinal/setFinal 簇
（tame_list.hl:14122/:14134/:14146/:14154/:14162/:14179/:14203） -/

/-- **HOL `nonFinals_fgraph`**（tame_list.hl:14122-:14132
`!f g. MEM f (nonFinals g) ==> MEM (FST f) (fgraph g)`）。
链 = List.mem_of_mem_filter（HOL Seq.mem_filter 槽）+ fgraphFaces
（批 2，tame_list.hl:184 fgraph_Faces 面）；fgraph ↦ facesVertexLists
（批 2 载体）。 -/
theorem nonFinalsFgraph {g : Kepler.Graphs.Graph} {F : Kepler.Graphs.Face}
    (hF : F ∈ nonFinals g) : F.vertices ∈ facesVertexLists g :=
  fgraphFaces (List.mem_of_mem_filter hF)

/-- **HOL `faceListAt_makeFaceFinal`**（tame_list.hl:14134-:14144
`!g f. faceListAt (makeFaceFinal f g) =
MAP (makeFaceFinalFaceList f) (faceListAt g)`）。
makeFaceFinal ↦ Kepler.Graphs.makeFaceFinal（FaceDivision AFP 层，
faceListAt 字段即 `g.faceListAt.map (makeFaceFinalFaceList f)`）——
HOL ETA_AX 面 Lean 原生 eta，定义性 rfl。 -/
theorem faceListAtMakeFaceFinal (f : Kepler.Graphs.Face) (g : Kepler.Graphs.Graph) :
    (makeFaceFinal f g).faceListAt = g.faceListAt.map (makeFaceFinalFaceList f) :=
  rfl

/-- **HOL `faces_makeFaceFinal`**（tame_list.hl:14146-:14151
`!g f. faces (makeFaceFinal f g) = makeFaceFinalFaceList f (faces g)`）
——faces 字段定义性 rfl。 -/
theorem facesMakeFaceFinal (f : Kepler.Graphs.Face) (g : Kepler.Graphs.Graph) :
    (makeFaceFinal f g).faces = makeFaceFinalFaceList f g.faces :=
  rfl

/-- **HOL `fst_setFinal`**（tame_list.hl:14154-:14159
`!f. FST (setFinal f) = FST f`）——批 56 sndSetFinal 对偶件；
FST ↦ `.vertices`（批 2 setFinalAlt 同层：setFinal 只改 isFinal 标记），
定义性 rfl。名撞记档：批 2 `fstSetFinal`（TameList2.lean:138）系
tame_list.hl:207 `MAP FST (replace f [setFinal f] vs) = MAP FST vs` 的
replace 面，本件按 setFinalFst 落。 -/
theorem setFinalFst (f : Kepler.Graphs.Face) :
    (setFinal f).vertices = f.vertices := rfl

/-- **HOL `filter_non_mem_setFinal`**（tame_list.hl:14162-:14177
`!vs v f. ~MEM v (FST f) ==> filter (\f. MEM v (FST f))
(replace f [setFinal f] vs) = filter (\f. MEM v (FST f)) vs`）。
载体：replace 批 17 replaceSpine；Seq.filter ↦ List.filter（decide
装箱）。证体：vs 归纳两支——命中支 `z = f`：replaceSpine if_pos +
filter_append + filter_eq_nil_iff（`~MEM v (setFinal f).vertices` 槽，
setFinal 字段面 defeq）+ nil_append + filter_cons_of_neg（~P z 槽）；
未命中支：replaceSpine if_neg + filter_cons 双发逐阶（新雷区一）+
归纳假设回喂（HOL COND_CASES_TAC 双分流同构）。 -/
theorem filterNonMemSetFinal (v : Kepler.Graphs.Vertex) (f : Kepler.Graphs.Face)
    (hf : v ∉ f.vertices) (vs : List Kepler.Graphs.Face) :
    (replaceSpine f [setFinal f] vs).filter (fun F => decide (v ∈ F.vertices))
      = vs.filter (fun F => decide (v ∈ F.vertices)) := by
  induction vs with
  | nil => rfl
  | cons z zs ih =>
    by_cases hz : z = f
    · have hzf : v ∉ z.vertices := by rw [hz]; exact hf
      have hsf : v ∉ (setFinal f).vertices := hf
      rw [replaceSpine, if_pos hz, List.filter_append,
        List.filter_eq_nil_iff.mpr (fun F hF => by
          rw [List.mem_singleton] at hF
          subst hF
          simpa using hsf),
        List.nil_append, List.filter_cons_of_neg (by simpa using hzf)]
    · rw [replaceSpine, if_neg hz, List.filter_cons, List.filter_cons, ih]

/-- 私件：replace 未命中形（HOL :14179 mem_fst_setFinal 证体 z = f /
~P f 支 `replace f [setFinal f] (filter P zs) = filter P zs` 槽的
机制面——x 不在表中 replace 恒等；批 56 filterReplace 同族体例）。 -/
private theorem replaceSpineMiss {α : Type*} [DecidableEq α] (x : α) (ys l : List α)
    (h : ∀ z ∈ l, z ≠ x) : replaceSpine x ys l = l := by
  induction l with
  | nil => rfl
  | cons z zs ih =>
    rw [replaceSpine, if_neg (h z (List.mem_cons_self ..))]
    exact congrArg (List.cons z) (ih fun w hw => h w (List.mem_cons_of_mem z hw))

/-- **HOL `mem_fst_setFinal`**（tame_list.hl:14179-:14201
`!vs v f. filter (\f. MEM v (FST f)) (replace f [setFinal f] vs) =
replace f [setFinal f] (filter (\f. MEM v (FST f)) vs)`）。
vs 归纳 + z=f/≠f × P 真/假 四分流（HOL COND_CASES_TAC 两层同构）：
z = f 支 replaceSpine if_pos（尾段保留——ys ++ zs 非递归）+
filter_append 展开 `filter P [setFinal f]`（P(setFinal f) = P f 字段面
defeq）后两翼 cons_append 归一即 rfl（P 真支）；P 假支槽 = 私件
replaceSpineMiss（f 被 filter P 尽出，HOL ASM_SIMP_TAC
[filter_non_mem_setFinal] 槽同面）；z ≠ f 支 filter_cons 双发逐阶 +
replaceSpine if_neg + 归纳假设回喂（新雷区一：右翼 filter 包裹支路待
filter_cons 发后再发）。 -/
theorem memFstSetFinal (v : Kepler.Graphs.Vertex) (f : Kepler.Graphs.Face)
    (vs : List Kepler.Graphs.Face) :
    (replaceSpine f [setFinal f] vs).filter (fun F => decide (v ∈ F.vertices))
      = replaceSpine f [setFinal f]
          (vs.filter (fun F => decide (v ∈ F.vertices))) := by
  induction vs with
  | nil => rfl
  | cons z zs ih =>
    by_cases hz : z = f
    · by_cases hP : decide (v ∈ f.vertices) = true
      · have hPz : decide (v ∈ z.vertices) = true := by rw [hz]; exact hP
        have hS : decide (v ∈ (setFinal f).vertices) = true := hP
        rw [replaceSpine, if_pos hz, List.filter_append,
          List.filter_cons_of_pos (p := fun (F : Kepler.Graphs.Face) => decide (v ∈ F.vertices)) hS,
          List.filter_cons_of_pos (p := fun (F : Kepler.Graphs.Face) => decide (v ∈ F.vertices)) hPz,
          List.cons_append, List.filter_nil, List.nil_append,
          replaceSpine, if_pos hz, List.cons_append, List.nil_append]
      · have hPz : ¬(decide (v ∈ z.vertices) = true) := by rw [hz]; exact hP
        have hS : ¬(decide (v ∈ (setFinal f).vertices) = true) := hP
        rw [replaceSpine, if_pos hz, List.filter_append,
          List.filter_cons_of_neg (p := fun (F : Kepler.Graphs.Face) => decide (v ∈ F.vertices)) hS,
          List.filter_nil, List.nil_append,
          List.filter_cons_of_neg (p := fun (F : Kepler.Graphs.Face) => decide (v ∈ F.vertices)) hPz]
        have hm : ∀ w ∈ List.filter (fun F => decide (v ∈ F.vertices)) zs, w ≠ f := by
          intro w hw hwf
          have hpw : decide (v ∈ w.vertices) = true := (List.mem_filter.mp hw).2
          rw [hwf] at hpw
          exact hP hpw
        rw [replaceSpineMiss f [setFinal f] _ hm]
    · by_cases hP : decide (v ∈ z.vertices) = true
      · rw [replaceSpine, if_neg hz,
          List.filter_cons_of_pos (p := fun (F : Kepler.Graphs.Face) => decide (v ∈ F.vertices)) hP,
          List.filter_cons_of_pos (p := fun (F : Kepler.Graphs.Face) => decide (v ∈ F.vertices)) hP,
          replaceSpine, if_neg hz, ih]
      · rw [replaceSpine, if_neg hz,
          List.filter_cons_of_neg (p := fun (F : Kepler.Graphs.Face) => decide (v ∈ F.vertices)) hP,
          List.filter_cons_of_neg (p := fun (F : Kepler.Graphs.Face) => decide (v ∈ F.vertices)) hP, ih]

/-- **HOL `countVertices_makeFaceFinal`**（tame_list.hl:14203-:14208
`!g f. countVertices (makeFaceFinal f g) = countVertices g`）——
countVertices 字段定义性 rfl。 -/
theorem countVerticesMakeFaceFinal (f : Kepler.Graphs.Face) (g : Kepler.Graphs.Graph) :
    (makeFaceFinal f g).countVertices = g.countVertices :=
  rfl

/-! ### §5 越章随收（tame_list.hl:14307；:14343 记档不落） -/

/-- **HOL `mem_minimalFace_fgraph`**（tame_list.hl:14307-:14317
`!g. ~finalGraph g ==> MEM (FST (minimalFace (nonFinals g))) (fgraph g)`）
——链 = minimalFaceFace（§2）+ fgraphFaces（批 2）；FST ↦ `.vertices`、
fgraph ↦ facesVertexLists（批 2 载体）。 -/
theorem memMinimalFaceFgraph (g : Kepler.Graphs.Graph)
    (hf : Kepler.Graphs.Graph.final g = false) :
    (minimalFace (nonFinals g)).vertices ∈ facesVertexLists g :=
  fgraphFaces (minimalFaceFace g hf)

/-! 记档不落：HOL `mem_faces_fgraph`（tame_list.hl:14343-:14347
`!f g. MEM f (faces g) ==> MEM (FST f) (fgraph g)`）——批 2
`fgraphFaces`（TameList2.lean:97，:184 fgraph_Faces 面）在册命中：
Lean 折算面（`F ∈ g.faces → F.vertices ∈ facesVertexLists g`）与本件
MEM 面逐字同语句（faces/Faces = set_of_list 面两前提 collapse，非
止损件）。 -/

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；十三件正文全绿零 sorryAx——
#print axioms Kepler.Text.TameSpine.listPairsCore
#print axioms Kepler.Text.TameSpine.planeGraphExP
#print axioms Kepler.Text.TameSpine.memMinimalVertex
#print axioms Kepler.Text.TameSpine.minimalFaceFace
#print axioms Kepler.Text.TameSpine.flagListSFlagList
#print axioms Kepler.Text.TameSpine.nonFinalsFgraph
#print axioms Kepler.Text.TameSpine.faceListAtMakeFaceFinal
#print axioms Kepler.Text.TameSpine.facesMakeFaceFinal
#print axioms Kepler.Text.TameSpine.setFinalFst
#print axioms Kepler.Text.TameSpine.filterNonMemSetFinal
#print axioms Kepler.Text.TameSpine.memFstSetFinal
#print axioms Kepler.Text.TameSpine.countVerticesMakeFaceFinal
#print axioms Kepler.Text.TameSpine.memMinimalFaceFgraph
-/
