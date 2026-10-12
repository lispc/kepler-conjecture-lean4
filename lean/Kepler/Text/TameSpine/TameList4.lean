/-
  Kepler.Text.TameSpine.TameList4 — B1 Tame_list 地基批 4：unadj / hideDups·showDups
  新定义块 + nextVertices 家族 + iso_list 运输家族
  （tamespine-port-plan §4 批次表 B1 行；接续批 3 = TameList3.lean，HOL
  :1469-2934，commit cdcc3ea2；本批从 `unadj` new_recursive_definition 起）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:2936-3642——`unadj` 定义起、
  hideDups/showDups/nextVertices/indexToVertexList 新定义块、option 基础件、
  indexToVertexList_enum capstone、inj_on/iso_list 运输家族、undup 家族、
  iso_list_all_uniq 收尾）：

  - 定义层：`unadj` :2936（bool ↦ Prop `Unadj`）、`image_hideDups` :2942
    （↦ `ImageHideDups`）、`showDups0`/`showDups`（tame_defs2.hl:642-650 ↦
    同名 def）、`enum_of_VertexList`（tame_defs2.hl:652 ↦ `enumOfVertexList`）；
  - option 基础件 :2944/:2952/:2960/:3097（some_inj_eq/hideDups_eq_nil/the_inj/
    not_isSome_NONE）；
  - hideDups↔showDups 往返 :2969-:2991（hideDupsRec_show/hideDups_show）；
  - nextVertices 家族 :3011-:3094（MEM_nextVertices/nextVertices0/
    indexf_nextVertices/nextVertices_indexf，HOL ITER ↦ Function.iterate）；
  - showDups 成员刻画 :3105-:3126（MEM_showDups0/MEM_showDups，HOL `all` ↦
    逐点 ∀ ∈ 形）；
  - `indexToVertexList_enum` :3145（A7 枚举层 capstone）；
  - inj_on 家族 :3202/:3221/:3317（inj_on_I/inj_on_o/inj_on_BIJ）；
  - iso_list 运输 :3211/:3275/:3328（iso_list_refl/trans/sym，载体 = 批 1
    `IsoListSpine`/`IsopListSpine`）；
  - undup 家族 :3232-:3274（undup_map_undup/list_of_elements_map/
    elements_of_list_MAP）；
  - `iso_list_all_uniq` :3617（all uniq 运输；别名 UEYETNI :3641 同体不另立）。

  批内分工记账（桥引不重移植；接批 1 头注清单）：
  - `map_good_list` :3403 / `find_face_map` :3450 / `hypermap_of_list_map`
    :3486：TameLp 先行件（la7_mapGoodList/la7_findFace_map/
    hypermapOfList_iso_map）+ 批 1 的 InjOn 桥形入口已落地；
  - `GNBEVVU` :3540 / `iso_list_good_list`（=PEUTLZH :3568）:3554：批 1 已真证；
  - `inj_on_INJ` :3308：HOL 库内部同义词（inj_on f s ↔ INJ f s univ），Lean
    `Set.InjOn` 即唯一载体，跳过（批 2 INJ_inj_on :468 同例）；
  - `IN_ELIM_SET_OF_LIST` :3609：set_of_list 成员同义词（set_of_list s u =
    MEM u s），Lean List/Set 成员定义性相同，跳过；
  - `iso_list_good_list_nodes`（别名 OISRWOF :3589）:3570：结论载体
    `GoodListNodes` 在 Assembly.lean:628 仍为 True 占位（W0-S11 缺口），
    占位载体上移植即空壳化，跳过（忠实化后经 number_of_nodes/iso_imp_hyp_iso
    桥 + 本批 undup 家族补）。

  载体折算（沿批 1-3 约定）：
  - `hideDups`/`hideDupsRec`/`indexToVertexList`：Kepler.Graphs.Enumerator 已有
    逐字同构 def（Enumerator.thy 载体），本批直接桥引、零重复移植；
    `nextVertex`/`nextVertices` ↦ `Kepler.Graphs.Face.nextVertex/nextVertices`
    （ITER 形桥 `faceNextVerticesIterate` 落本模块）；`next_el` ↦
    Kepler.Assembly.nextEl；
  - `filter isSome` ↦ `List.filter Option.isSome`；`the` ↦ `Option.get!`
    （配 `[Inhabited α]`，越界 junk 按默认值约定吸收，批 3 `head!` 同款）；
  - `undup`（HOL 递归形）↦ Lean `List.eraseDups`（保首现；递归形状差异的记账
    见批 2 undupCat_mem 条与下段诚实记账）；
  - `uniq` ↦ `List.Nodup`；`all P l` ↦ `∀ t ∈ l, P t`。

  诚实记账（陈述收窄/笔误补全/载体约定）：
  - `unadj`/`image_hideDups` 的 HOL bool 值按 Prop 落（Unadj/ImageHideDups），
    合取语境无语义损失；`Unadj` 按「空表/单元素表为 True、长表首二相异」
    三支递归直写，与 HOL 条件式逐点等价（HD 的 junk 值由 t = [] 分支挡死）；
  - `hideDupsRec_show`/`hideDups_show`/`indexToVertexList_enum`/`MEM_showDups*`
    的 `the` 前提件按 `Option.get!` 落（isSome 前提下与 HOL the 逐字同义）；
    `showDups`/`showDups0` 在头元素为 NONE 时的 junk 行为按 Inhabited 默认值
    吸收（本批各件前提恰挡住该分支，无 junk 语义损失）；
  - `iso_list_sym` 的两组 `set_of_list … ⊆ elements_of_list` 前提按逐点
    `∀ p ∈ flatten, p.1/p.2 ∈ elementsOfList` 落（成员谓词等价）；逆映射存在性
    经 Classical.choose 显式构造（HOL INVERSE 函数子的 choice 语义，本批
    `existsInverseOfInjOn` 私件）；L/N 两方程的组合用 List.map_congr_left +
    List.map_id 替代 HOL MAP_EQ/MAP_I 链；
  - `undup_map_undup`：HOL undup 与 Lean eraseDups 同为保首现去重但递归形状
    不同（HOL 按 mem 分支、Lean 按 filter 递归），本批按 eraseDups 陈述真证
    （本件按长度归纳落；核心 = 私件 `eraseDupsMapFilterCommute` 的长度归纳 +
    `filterSwap` 交换律 + 「f x = f a 蕴含 x ≠ a」自过滤；两语义下本件均真，
    无收窄）；`list_of_elements_map` 在 TameLp listOfElements
    （flatten.eraseDups）载体上以同一私件收口；
  - `nextVertices0` 在 Lean 载体下为 rfl（Face.nextVertices 的 0 支），保留
    定理名以对齐 HOL 清单；
  - `indexf_nextVertices`/`nextVertices_indexf` 的 uniq 前提 ↦
    `f.vertices.Nodup`；HOL `sizel (FST f)` ↦ `f.vertices.length`。

  红线遵守：本模块零 sorry、零既有文件触碰、零 git 写操作。
-/

import Kepler.Text.TameSpine.TameList3

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph hideDups hideDupsRec indexToVertexList)
open Kepler.Assembly (nextEl)
open Kepler.Text.TameLp (elementsOfList listOfElements)

variable {α : Type*}

/-! ### §0 定义层（tame_list.hl:2936-2942；tame_defs2.hl:642-654） -/

/-- HOL `unadj`（tame_list.hl:2936
`unadj [] = T /\ unadj (h::t) = if t = [] then T else ~(h = HD t) /\ unadj t`）
逐句镜像（bool ↦ Prop；长表支按 `HD (h'::t) = h'` 直写）。 -/
def Unadj : List α → Prop
  | [] => True
  | [_] => True
  | h :: h' :: t => h ≠ h' ∧ Unadj (h' :: t)

/-- HOL `showDups0`（tame_defs2.hl:642
`showDups0 a [] = [] /\ showDups0 a (b::bs) = if b = NONE then a :: showDups0 a bs
else (the b) :: showDups0 (the b) bs`）逐句镜像（NONE 分支按模式匹配直写）。 -/
def showDups0 (a : α) : List (Option α) → List α
  | [] => []
  | none :: bs => a :: showDups0 a bs
  | some b :: bs => b :: showDups0 b bs

/-- HOL `showDups`（tame_defs2.hl:648
`showDups [] = [] /\ showDups (b::bs) = showDups0 (the b) (b::bs)`）逐句镜像
（`the` ↦ `Option.get!`，junk 按 Inhabited 默认值吸收）。 -/
def showDups [Inhabited α] : List (Option α) → List α
  | [] => []
  | b :: bs => showDups0 b.get! (b :: bs)

/-- HOL `image_hideDups`（tame_list.hl:2942
`image_hideDups s = (s = [] \/ (unadj (filter isSome s) /\ isSome (HD s)))`）
逐句镜像。 -/
def ImageHideDups (s : List (Option α)) : Prop :=
  s = [] ∨ (Unadj (s.filter Option.isSome) ∧ s.head!.isSome)

/-- HOL `enum_of_VertexList`（tame_defs2.hl:652
`enum_of_VertexList f (v:A) vs = MAP (\u. indexf v u f) (showDups vs)`）逐句镜像
（`indexf` = 批 3 载体；HOL 原型结果域即 num——本定义对泛型 α 落 List ℕ，
与消费点 indexToVertexListEnum 的 Vertex=ℕ 实例化一致）。 -/
def enumOfVertexList [BEq α] [LawfulBEq α] [Inhabited α] (f : List α) (v : α)
    (vs : List (Option α)) : List ℕ :=
  (showDups vs).map (fun u => indexf v u f)

/-! ### §1 option 基础件（tame_list.hl:2944/:2952/:2960/:3097） -/

/-- HOL `some_inj_eq`（tame_list.hl:2944 `SOME x = SOME y <=> x = y`）。 -/
theorem someInjEq {x y : α} : Option.some x = Option.some y ↔ x = y :=
  ⟨Option.some.inj, congrArg Option.some⟩

/-- HOL `hideDups_eq_nil`（tame_list.hl:2952 `hideDups s = [] <=> s = []`；
`hideDups` = Kepler.Graphs.Enumerator 同名载体）。 -/
theorem hideDupsEqNil [BEq α] {s : List α} : hideDups s = [] ↔ s = [] := by
  cases s with
  | nil => simp [hideDups]
  | cons b bs => simp [hideDups]

/-- HOL `the_inj`（tame_list.hl:2960
`isSome a /\ isSome b ==> (the a = the b <=> a = b)`）。 -/
theorem theInj [Inhabited α] {a b : Option α} (ha : a.isSome) (hb : b.isSome) :
    a.get! = b.get! ↔ a = b := by
  cases a with
  | none => simp at ha
  | some x =>
    cases b with
    | none => simp at hb
    | some y => simp

/-- HOL `not_isSome_NONE`（tame_list.hl:3097 `isSome x <=> ~(x = NONE)`）。 -/
theorem isSomeIffNeNone {x : Option α} : x.isSome ↔ x ≠ none := by
  cases x <;> simp

/-! ### §2 hideDups ↔ showDups 往返（tame_list.hl:2969-:2991） -/

/-- 私件：全 NONE 表上 `hideDupsRec (a) (showDups0 a t) = t` 无前提成立
（hideDupsRec_show 的退化支；HOL 证明中由 `ASM_MESON_TAC` 吸收的分支）。 -/
private theorem hideDupsRecShowDups0OfAllNone [BEq α] [LawfulBEq α]
    {t : List (Option α)} (hall : ∀ x ∈ t, x = none) (a : α) :
    hideDupsRec a (showDups0 a t) = t := by
  induction t with
  | nil => rfl
  | cons b bs ih =>
    have hb : b = none := hall b List.mem_cons_self
    subst hb
    simp only [showDups0, hideDupsRec, beq_self_eq_true, if_true]
    rw [ih (fun y hy => hall y (List.mem_cons_of_mem none hy))]

/-- HOL `hideDupsRec_show`（tame_list.hl:2969
`~(filter isSome t = []) ==> ~(a = HD (filter isSome t)) /\ unadj (filter isSome t)
==> isSome a ==> hideDupsRec (the a) (showDups0 (the a) t) = t`）。
四前提按 (t, a) 逐槽平铺（归纳需对 a 泛化）。 -/
theorem hideDupsRecShow [Inhabited α] [BEq α] [LawfulBEq α] :
    ∀ (t : List (Option α)) (a : Option α),
      t.filter Option.isSome ≠ [] →
      Unadj (t.filter Option.isSome) →
      a ≠ (t.filter Option.isSome).head! →
      a.isSome →
      hideDupsRec a.get! (showDups0 a.get! t) = t := by
  intro t
  induction t with
  | nil => intro a hne; exact absurd rfl hne
  | cons b bs ih =>
    intro a hne hadj hna ha
    cases b with
    | none =>
      have hf : (Option.none :: bs).filter Option.isSome = bs.filter Option.isSome := by
        simp [List.filter_cons]
      rw [hf] at hne hadj hna
      show (if a.get! == a.get! then none else some a.get!)
          :: hideDupsRec a.get! (showDups0 a.get! bs) = none :: bs
      simp only [beq_self_eq_true, if_true]
      rw [ih a hne hadj hna ha]
    | some x =>
      have hf : (Option.some x :: bs).filter Option.isSome
          = Option.some x :: bs.filter Option.isSome := by
        simp [List.filter_cons]
      rw [hf] at hne hadj hna
      have hcontra : ¬(a.get! = x) := by
        intro he
        have ha' : a = Option.some x := by
          cases a with
          | none => exact absurd ha (by simp)
          | some x' =>
            have hx' : x' = x := he
            exact congrArg Option.some hx'
        exact hna (by rw [ha']; simp [List.filter_cons])
      show (if a.get! == x then none else some x)
          :: hideDupsRec x (showDups0 x bs) = Option.some x :: bs
      simp only [beq_iff_eq, hcontra, if_false]
      congr 1
      cases hf2 : bs.filter Option.isSome with
      | nil =>
        have hall : ∀ y ∈ bs, y = none := by
          intro y hy
          have hy' : ¬(y.isSome = true) :=
            List.filter_eq_nil_iff.mp hf2 y hy
          cases y with
          | none => rfl
          | some y' => simp at hy'
        rw [hideDupsRecShowDups0OfAllNone hall x]
      | cons r0 r1 =>
        rw [hf2] at hadj
        obtain ⟨hu1, hu2⟩ := hadj
        refine ih (Option.some x) (by rw [hf2]; exact List.cons_ne_nil r0 r1)
          (by rw [hf2]; exact hu2) ?_ rfl
        rw [hf2]; exact hu1

/-- HOL `hideDups_show`（tame_list.hl:2991
`image_hideDups s ==> hideDups (showDups s) = s`）。 -/
theorem hideDupsShow [Inhabited α] [BEq α] [LawfulBEq α] {s : List (Option α)}
    (h : ImageHideDups s) : hideDups (showDups s) = s := by
  cases s with
  | nil => rfl
  | cons b bs =>
    rcases h with h0 | ⟨hadj, hhead⟩
    · exact absurd h0 (List.cons_ne_nil b bs)
    · rw [List.head!_cons] at hhead
      cases hb : b with
      | none => rw [hb] at hhead; simp at hhead
      | some x =>
        subst hb
        show hideDups (showDups0 x (Option.some x :: bs)) = Option.some x :: bs
        show hideDups (x :: showDups0 x bs) = Option.some x :: bs
        show Option.some x :: hideDupsRec x (showDups0 x bs) = Option.some x :: bs
        congr 1
        have hf : (Option.some x :: bs).filter Option.isSome
            = Option.some x :: bs.filter Option.isSome := by
          simp [List.filter_cons]
        rw [hf] at hadj
        cases hf2 : bs.filter Option.isSome with
        | nil =>
          have hall : ∀ y ∈ bs, y = none := by
            intro y hy
            have hy' : ¬(y.isSome = true) := List.filter_eq_nil_iff.mp hf2 y hy
            cases y with
            | none => rfl
            | some y' => simp at hy'
          rw [hideDupsRecShowDups0OfAllNone hall x]
        | cons r0 r1 =>
          rw [hf2] at hadj
          obtain ⟨hu1, hu2⟩ := hadj
          refine hideDupsRecShow bs (Option.some x)
            (by rw [hf2]; exact List.cons_ne_nil r0 r1) (by rw [hf2]; exact hu2) ?_ rfl
          rw [hf2]; exact hu1

/-! ### §3 nextVertices 家族（tame_list.hl:3011-:3094） -/

/-- 载体桥：HOL `nextVertices f n v = ITER n (nextVertex f) v`
（tame_defs.hl:360）的 iterate 形——`Kepler.Graphs.Face.nextVertices`
（Graph.thy 同名递归）与之逐点相等。 -/
theorem faceNextVerticesIterate (f : Kepler.Graphs.Face) (n : ℕ)
    (v : Kepler.Graphs.Vertex) :
    f.nextVertices n v = (f.nextVertex)^[n] v := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show f.nextVertex (f.nextVertices m v) = f.nextVertex^[m + 1] v
    rw [ih, Function.iterate_succ_apply']

/-- 私件：`nextVertex` 迭代不出面（MEM_nextVertices 的归纳引擎；
GraphProps.nextVertex_in_face 的迭代形）。 -/
private theorem memNextVertexIterate {f : Kepler.Graphs.Face} {v : Kepler.Graphs.Vertex}
    (hv : v ∈ f.vertices) :
    ∀ m : ℕ, (f.nextVertex)^[m] v ∈ f.vertices := by
  intro m
  induction m with
  | zero => exact hv
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact Kepler.Graphs.nextVertex_in_face ih

/-- 私件：nextVertex 迭代与 nextEl 迭代在轨道上逐点重合
（批 3 nextVertexNextEl 的迭代提升；HOL `nextVertex_next_el` 的 ITER 形）。 -/
private theorem nextElIterateCongr {f : Kepler.Graphs.Face} {v : Kepler.Graphs.Vertex}
    (hv : v ∈ f.vertices) (n : ℕ) :
    (f.nextVertex)^[n] v = (nextEl f.vertices)^[n] v := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have hm : (f.nextVertex)^[m] v ∈ f.vertices := memNextVertexIterate hv m
    rw [ih] at hm
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact nextVertexNextEl hm

/-- HOL `MEM_nextVertices`（tame_list.hl:3011
`MEM v (FST f) ==> MEM (nextVertices f n v) (FST f)`）。 -/
theorem memNextVertices {f : Kepler.Graphs.Face} {v : Kepler.Graphs.Vertex}
    (hv : v ∈ f.vertices) (n : ℕ) : f.nextVertices n v ∈ f.vertices := by
  rw [faceNextVerticesIterate]
  exact memNextVertexIterate hv n

/-- HOL `nextVertices0`（tame_list.hl:3027 `nextVertices f 0 v = v`；
Lean 载体下定义性）。 -/
theorem nextVerticesZero (f : Kepler.Graphs.Face) (v : Kepler.Graphs.Vertex) :
    f.nextVertices 0 v = v := rfl

/-- HOL `indexf_nextVertices`（tame_list.hl:3035
`MEM v (FST f) /\ uniq (FST f) /\ n < sizel (FST f)
==> indexf v (nextVertices f n v) (FST f) = n`）。
HOL 的 next_el↔indexf 归纳在 Lean 载体下由批 3 `nextElnIndexf` 一步收口。 -/
theorem indexfNextVertices {f : Kepler.Graphs.Face} {v : Kepler.Graphs.Vertex}
    (hv : v ∈ f.vertices) (hnd : f.vertices.Nodup) {n : ℕ}
    (hn : n < f.vertices.length) :
    indexf v (f.nextVertices n v) f.vertices = n := by
  rw [faceNextVerticesIterate, nextElIterateCongr hv n]
  have hy : (nextEl f.vertices)^[n] v ∈ f.vertices := by
    rw [← nextElIterateCongr hv n, ← faceNextVerticesIterate]
    exact memNextVertices hv n
  exact nextElnIndexf hv hy hnd rfl hn

/-- HOL `nextVertices_indexf`（tame_list.hl:3068
`uniq (FST f) /\ MEM v (FST f) /\ MEM w (FST f)
==> nextVertices f (indexf v w (FST f)) v = w`）。
HOL 的 indexf_add_left 归纳由批 3 `indexfN` 一步收口。 -/
theorem nextVerticesIndexf {f : Kepler.Graphs.Face} {v w : Kepler.Graphs.Vertex}
    (hv : v ∈ f.vertices) (hw : w ∈ f.vertices) (hnd : f.vertices.Nodup) :
    f.nextVertices (indexf v w f.vertices) v = w := by
  rw [faceNextVerticesIterate, nextElIterateCongr hv]
  exact indexfN hv hw hnd

/-! ### §4 showDups 成员刻画（tame_list.hl:3105-:3126） -/

/-- HOL `MEM_showDups0`（tame_list.hl:3105
`all (\t. (t = a) \/ MEM t (MAP the (filter isSome vs))) (showDups0 a vs)`）；
HOL `all` 按逐点 ∀ ∈ 形落。 -/
theorem memShowDups0 [Inhabited α] :
    ∀ (a : α) (vs : List (Option α)),
      ∀ t ∈ showDups0 a vs, t = a ∨ t ∈ (vs.filter Option.isSome).map Option.get! := by
  intro a vs
  induction vs generalizing a with
  | nil => intro t ht; cases ht
  | cons b bs ih =>
    cases b with
    | none =>
      have hf : (Option.none :: bs).filter Option.isSome = bs.filter Option.isSome := by
        simp [List.filter_cons]
      intro t ht
      simp only [showDups0, List.mem_cons] at ht
      rw [hf]
      rcases ht with ht | ht
      · exact Or.inl ht
      · exact ih a t ht
    | some c =>
      have hf : (Option.some c :: bs).filter Option.isSome
          = Option.some c :: bs.filter Option.isSome := by
        simp [List.filter_cons]
      intro t ht
      simp only [showDups0, List.mem_cons] at ht
      rw [hf]
      rcases ht with ht | ht
      · refine Or.inr ?_
        refine List.mem_map.mpr ⟨Option.some c, ?_, ht.symm⟩
        simp
      · rcases ih c t ht with ht | ht
        · refine Or.inr ?_
          refine List.mem_map.mpr ⟨Option.some c, ?_, ht.symm⟩
          simp
        · refine Or.inr ?_
          rcases List.mem_map.mp ht with ⟨y, hy, hyt⟩
          refine List.mem_map.mpr ⟨y, ?_, hyt⟩
          simp only [Option.isSome_some, ↓reduceIte, List.mem_cons]
          exact Or.inr hy

/-- HOL `MEM_showDups`（tame_list.hl:3126
`~(vs = []) ==> (isSome (HD vs)) ==>
all (\t. MEM t (MAP the (filter isSome vs))) (showDups vs)`）。 -/
theorem memShowDups [Inhabited α] {vs : List (Option α)}
    (h : vs ≠ [] → vs.head!.isSome) :
    ∀ t ∈ showDups vs, t ∈ (vs.filter Option.isSome).map Option.get! := by
  cases vs with
  | nil => intro t ht; cases ht
  | cons b bs =>
    have hbis : (b :: bs).head!.isSome := h (List.cons_ne_nil b bs)
    rw [List.head!_cons] at hbis
    obtain ⟨x, hx⟩ : ∃ x, b = Option.some x := by
      cases hb2 : b with
      | none => rw [hb2] at hbis; simp at hbis
      | some x => exact ⟨x, rfl⟩
    subst hx
    have hfilt : (Option.some x :: bs).filter Option.isSome
        = Option.some x :: bs.filter Option.isSome := by
      simp [List.filter_cons]
    intro t ht
    have ht' : t ∈ showDups0 x (Option.some x :: bs) := ht
    rw [hfilt]
    have hall := memShowDups0 x (Option.some x :: bs) t ht'
    rw [hfilt] at hall
    rcases hall with ht2 | ht2
    · refine List.mem_map.mpr ⟨Option.some x, ?_, ht2.symm⟩
      simp
    · rcases List.mem_map.mp ht2 with ⟨y, hy, hyt⟩
      exact List.mem_map.mpr ⟨y, hy, hyt⟩

/-! ### §5 indexToVertexList_enum capstone（tame_list.hl:3145） -/

/-- **HOL `indexToVertexList_enum`**（tame_list.hl:3145
`uniq (FST f) /\ MEM v (FST f) /\ image_hideDups vs /\
all (\t. MEM (the t) (FST f)) (filter isSome vs) ==>
indexToVertexList f v (enum_of_VertexList (FST f) v vs) = vs`）。

证明同 HOL：MAP 复合层按 `nextVertices_indexf` 逐点化简为 MAP I，再由
`hideDups_show` 收口（`indexToVertexList` = Kepler.Graphs.Enumerator 载体）。 -/
theorem indexToVertexListEnum {f : Kepler.Graphs.Face} {v : Kepler.Graphs.Vertex}
    {vs : List (Option Kepler.Graphs.Vertex)}
    (hnd : f.vertices.Nodup) (hv : v ∈ f.vertices) (hid : ImageHideDups vs)
    (hall : ∀ t ∈ vs.filter Option.isSome, t.get! ∈ f.vertices) :
    indexToVertexList f v (enumOfVertexList f.vertices v vs) = vs := by
  have hhead : vs ≠ [] → vs.head!.isSome := by
    intro hne
    cases vs with
    | nil => exact absurd rfl hne
    | cons c cs =>
      rcases hid with h0 | ⟨_, h2⟩
      · exact absurd h0 (List.cons_ne_nil c cs)
      · exact h2
  have hmem : ∀ u ∈ showDups vs, u ∈ f.vertices := by
    intro u hu
    have hu' : u ∈ (vs.filter Option.isSome).map Option.get! :=
      memShowDups hhead u hu
    rcases List.mem_map.mp hu' with ⟨t, ht, hut⟩
    rw [← hut]; exact hall t ht
  show hideDups ((enumOfVertexList f.vertices v vs).map (fun k => f.nextVertices k v))
      = vs
  show hideDups ((((showDups vs).map (fun u => indexf v u f.vertices))).map
      (fun k => f.nextVertices k v)) = vs
  rw [List.map_map, List.map_congr_left
    (f := (fun k => f.nextVertices k v) ∘ (fun u => indexf v u f.vertices)) (g := id)
    (fun u hu => nextVerticesIndexf hv (hmem u hu) hnd), List.map_id]
  exact hideDupsShow hid

/-! ### §6 inj_on 家族与 iso_list 运输（tame_list.hl:3202-:3400/:3617） -/

/-- HOL `inj_on_I`（tame_list.hl:3202 `inj_on I L`）。 -/
theorem injOnI (S : Set ℕ) : Set.InjOn id S := fun _ _ _ _ h => h

/-- HOL `iso_list_refl`（tame_list.hl:3211 `iso_list L L`；存在 φ 形，
证人 φ = id）。 -/
theorem isoListSpineRefl (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) :
    IsoListSpine L L N N :=
  ⟨id, fun _ _ _ _ h => h, by simp, by simp⟩

/-- HOL `inj_on_o`（tame_list.hl:3221
`inj_on phi X /\ inj_on phi' (IMAGE phi X) ==> inj_on (phi' o phi) X`）。 -/
theorem injOnComp {X : Set ℕ} {phi phi' : ℕ → ℕ}
    (h : Set.InjOn phi X) (h' : Set.InjOn phi' (phi '' X)) :
    Set.InjOn (phi' ∘ phi) X :=
  Set.InjOn.comp h' h (Set.mapsTo_image phi X)

/-- 私件：filter 交换律（批 2 filterConj 的 Bool.and_comm 推论）。 -/
private theorem filterSwap {p q : α → Bool} (l : List α) :
    (l.filter q).filter p = (l.filter p).filter q := by
  rw [filterConj (f := p) (g := q) l, filterConj (f := q) (g := p) l]
  congr 1
  funext x
  simp [Bool.and_comm]

/-- 私件（undup 家族引擎）：`(l.eraseDups).map f` 经 q = `!(· == f a)` 过滤后
等于 `(l.filter q).eraseDups` 的 f 像（eraseDupsMapEraseDups 的长度归纳核；
HOL undup_map_undup 的 MEMf_MAP/mem_undup 步在本载体下的重排）。 -/
private theorem eraseDupsMapFilterCommute [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {a : α} {f : α → β} :
    ∀ (n : ℕ) (l : List α), l.length ≤ n →
      ((l.eraseDups.map f).filter (fun y => !(y == f a)))
        = (l.filter (fun x => !(f x == f a))).eraseDups.map f := by
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => rfl
    | cons b t => simp at hl
  | succ n ih =>
    intro l hl
    cases l with
    | nil => rfl
    | cons b t =>
      have htl : t.length ≤ n := by simpa using hl
      have hfl : (t.filter (fun x => !(x == b))).length ≤ n := by
        have h1 := List.length_filter_le (fun x => !(x == b)) t
        exact h1.trans htl
      cases hqb : (f b == f a) with
      | true =>
        have hnoB : (t.filter (fun x => !(f x == f a))).filter (fun x => !(x == b))
            = t.filter (fun x => !(f x == f a)) := by
          refine List.filter_eq_self.mpr (fun y hy => ?_)
          have hyq : ¬(f y = f a) := by
            have h2 := (List.mem_filter.mp hy).2
            simpa [beq_iff_eq] using h2
          have hfb : f b = f a := by simpa [beq_iff_eq] using hqb
          show (!(y == b)) = true
          cases hyb : (y == b) with
          | true =>
            have hyb' : y = b := by simpa [beq_iff_eq] using hyb
            exact absurd (by rw [hyb']; exact hfb) hyq
          | false => rfl
        have hlhs : (((b :: t).eraseDups.map f).filter (fun y => !(y == f a)))
            = (t.filter (fun x => !(f x == f a))).eraseDups.map f := by
          rw [List.eraseDups_cons, List.map_cons, List.filter_cons, hqb, Bool.not_true,
            if_neg (by simp)]
          rw [ih (t.filter (fun x => !(x == b))) hfl, filterSwap, hnoB]
        have hrhs : (((b :: t).filter (fun x => !(f x == f a))).eraseDups.map f)
            = (t.filter (fun x => !(f x == f a))).eraseDups.map f := by
          rw [List.filter_cons, hqb, Bool.not_true, if_neg (by simp)]
        rw [hlhs, hrhs]
      | false =>
        have hlhs : (((b :: t).eraseDups.map f).filter (fun y => !(y == f a)))
            = (f b :: List.map f (List.eraseDups
              ((t.filter (fun x => !(f x == f a))).filter
                (fun x => !(x == b))))) := by
          rw [List.eraseDups_cons, List.map_cons, List.filter_cons, hqb, Bool.not_false,
            if_pos rfl]
          rw [ih (t.filter (fun x => !(x == b))) hfl, filterSwap]
        have hrhs : (((b :: t).filter (fun x => !(f x == f a))).eraseDups.map f)
            = (f b :: List.map f (List.eraseDups
              ((t.filter (fun x => !(f x == f a))).filter
                (fun x => !(x == b))))) := by
          rw [List.filter_cons, hqb, Bool.not_false, if_pos rfl]
          rw [List.eraseDups_cons, List.map_cons]
        rw [hlhs, hrhs]

/-- HOL `undup_map_undup`（tame_list.hl:3232
`undup (MAP f (undup s)) = undup (MAP f s)`）的 eraseDups 载体形。
HOL 证明按 undup 的 mem 分支递归；Lean eraseDups 按 filter 递归，此处以
`eraseDupsMapFilterCommute`（长度归纳）+ filter 交换律 + 「f x = f a 蕴含
x = a 不成立方向」的自过滤收口（诚实记账见头注）；本件按长度归纳落（cons 步
的 RHS-inner 经该私件 + ih 的 filter q' as 实例闭合）。 -/
theorem eraseDupsMapEraseDups [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n →
      (l.map f).eraseDups = (l.eraseDups.map f).eraseDups := by
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => rfl
    | cons b t => simp at hl
  | succ n ih =>
    intro l hl
    cases l with
    | nil => rfl
    | cons a as =>
      have has : as.length ≤ n := by simpa using hl
      have hq'a : ∀ x ∈ List.filter (fun x => !(f x == f a)) as,
          (fun x => !(x == a)) x = true := by
        intro x hx
        have hf : ¬(f x = f a) := by
          have h2 := (List.mem_filter.mp hx).2
          simpa [beq_iff_eq] using h2
        show (!(x == a)) = true
        cases hxa : (x == a) with
        | true =>
          have hxa' : x = a := by simpa [beq_iff_eq] using hxa
          exact absurd (show f x = f a by rw [hxa']) hf
        | false => rfl
      have hsw : List.filter (fun x => !(f x == f a))
          (List.filter (fun x => !(x == a)) as)
          = List.filter (fun x => !(f x == f a)) as := by
        rw [← filterSwap (p := fun x => !(x == a)) (q := fun x => !(f x == f a)) as]
        exact List.filter_eq_self.mpr hq'a
      have hfm : List.filter (fun y => !(y == f a)) (as.map f)
          = List.map f (List.filter (fun x => !(f x == f a)) as) :=
        List.filter_map
      have hfl' : (List.filter (fun x => !(x == a)) as).length ≤ n :=
        (List.length_filter_le (fun x => !(x == a)) as).trans has
      have hih' : List.filter (fun y => !(y == f a))
          (List.map f (List.eraseDups (List.filter (fun x => !(x == a)) as)))
          = List.map f (List.eraseDups
              (List.filter (fun x => !(f x == f a)) (List.filter (fun x => !(x == a)) as))) :=
        eraseDupsMapFilterCommute (f := f) (a := a) _ _ hfl'
      show (f a :: (as.map f)).eraseDups = (((a :: as).eraseDups).map f).eraseDups
      rw [List.eraseDups_cons, List.eraseDups_cons, List.map_cons, List.eraseDups_cons,
        hfm, hih', hsw, ← ih (List.filter (fun x => !(f x == f a)) as)
          ((List.length_filter_le (fun x => !(f x == f a)) as).trans has)]

/-- HOL `list_of_elements_map`（tame_list.hl:3254
`undup (MAP f (list_of_elements s)) = list_of_elements (MAP (MAP f) s)`）的
TameLp listOfElements（flatten.eraseDups）载体形。 -/
theorem listOfElementsMap (L : fgraph ℕ) (phi : ℕ → ℕ) :
    ((listOfElements L).map phi).eraseDups = listOfElements (L.map (List.map phi)) := by
  show ((L.flatten.eraseDups).map phi).eraseDups
      = ((L.map (List.map phi)).flatten).eraseDups
  rw [← mapFlattenSpine]
  exact (eraseDupsMapEraseDups phi _ (List.flatten L) (Nat.le_refl _)).symm

/-- HOL `elements_of_list_MAP`（tame_list.hl:3264
`elements_of_list (MAP (MAP phi) s) = IMAGE phi (elements_of_list s)`）。
（批 1 injOn_elementsOfList_iff 同域的集合等式形。） -/
theorem elementsOfListMap (L : fgraph ℕ) (phi : ℕ → ℕ) :
    elementsOfList (L.map (List.map phi)) = phi '' elementsOfList L := by
  refine Set.ext (fun y => ?_)
  constructor
  · intro hy
    have h1 : y ∈ ((L.map (List.map phi)).flatten).eraseDups := hy
    have h2 : y ∈ (L.map (List.map phi)).flatten := List.mem_eraseDups.mp h1
    rw [← mapFlattenSpine] at h2
    rcases List.mem_map.mp h2 with ⟨x, hx, hxy⟩
    exact (Set.mem_image _ _ _).mpr ⟨x, List.mem_eraseDups.mpr hx, hxy⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := (Set.mem_image _ _ _).mp hy
    have h3 : x ∈ L.flatten := List.mem_eraseDups.mp hx
    refine hxy ▸ ?_
    show phi x ∈ elementsOfList (L.map (List.map phi))
    have h4 : phi x ∈ (L.map (List.map phi)).flatten := by
      rw [← mapFlattenSpine]
      exact List.mem_map.mpr ⟨x, h3, rfl⟩
    exact List.mem_eraseDups.mpr h4

/-- HOL `iso_list_trans`（tame_list.hl:3275
`iso_list L L' /\ iso_list L' L'' ==> iso_list L L''`）。
证人 φ'' ∘ φ；inj_on_o + elements_of_list_MAP 替代 HOL 同名链。 -/
theorem isoListSpineTrans {L₁ L₂ L₃ : fgraph ℕ} {N₁ N₂ N₃ : List (List (ℕ × ℕ))}
    (h₁ : IsoListSpine L₁ L₂ N₁ N₂) (h₂ : IsoListSpine L₂ L₃ N₂ N₃) :
    IsoListSpine L₁ L₃ N₁ N₃ := by
  obtain ⟨phi, hinj, hL₂, hN₂⟩ := h₁
  obtain ⟨psi, hinj', hL₃, hN₃⟩ := h₂
  have hmap : elementsOfList L₂ = phi '' elementsOfList L₁ := by
    rw [hL₂]; exact elementsOfListMap L₁ phi
  refine ⟨psi ∘ phi, Set.InjOn.comp hinj' hinj (fun x hx => by
    rw [hmap]; exact Set.mem_image_of_mem _ hx), ?_, ?_⟩
  · rw [hL₃, hL₂]
    have e : (L₁.map (List.map phi)).map (List.map psi)
        = L₁.map (List.map (psi ∘ phi)) := by
      rw [List.map_map]
      refine List.map_congr_left (fun s _ => List.map_map)
    rw [e]
  · rw [hN₃, hN₂]
    have e : (N₁.map (fun s => s.map (fun u => (phi u.1, phi u.2)))).map
        (List.map (fun u => (psi u.1, psi u.2)))
        = N₁.map (List.map (fun u => ((psi ∘ phi) u.1, (psi ∘ phi) u.2))) := by
      rw [List.map_map]
      refine List.map_congr_left (fun s _ => List.map_map)
    rw [e]

/-- HOL `inj_on_BIJ`（tame_list.hl:3317
`inj_on f s ==> BIJ f s (IMAGE f s)`）。 -/
theorem injOnBijOnImage {S : Set ℕ} {phi : ℕ → ℕ} (h : Set.InjOn phi S) :
    Set.BijOn phi S (phi '' S) :=
  ⟨Set.mapsTo_image phi S, h, fun y hy => by
    rcases (Set.mem_image _ _ _).mp hy with ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩⟩

/-- 私件：单射 `phi` 在像集上的逆映射存在性
（HOL `INVERSE`/`INVERSE_BIJ`/`INVERSE_XY` 组合的 Classical.choose 显式形，
iso_list_sym 的证人构造）。 -/
private theorem existsInverseOfInjOn {S T : Set ℕ} {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi S) (hsurj : ∀ y ∈ T, ∃ x ∈ S, phi x = y) :
    ∃ phi' : ℕ → ℕ, Set.InjOn phi' T ∧ ∀ x ∈ S, phi' (phi x) = x := by
  classical
  refine ⟨fun y => if h : ∃ x ∈ S, phi x = y then Classical.choose h else 0, ?_, ?_⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    have h₁ : ∃ x ∈ S, phi x = y₁ := hsurj y₁ hy₁
    have h₂ : ∃ x ∈ S, phi x = y₂ := hsurj y₂ hy₂
    have e₁ : (if h : ∃ x ∈ S, phi x = y₁ then Classical.choose h else 0)
        = Classical.choose h₁ := dif_pos h₁
    have e₂ : (if h : ∃ x ∈ S, phi x = y₂ then Classical.choose h else 0)
        = Classical.choose h₂ := dif_pos h₂
    have hc : Classical.choose h₁ = Classical.choose h₂ := by
      rw [← e₁, ← e₂]; exact heq
    have p₁ : phi (Classical.choose h₁) = y₁ := (Classical.choose_spec h₁).2
    have p₂ : phi (Classical.choose h₂) = y₂ := (Classical.choose_spec h₂).2
    rw [← p₁, ← p₂, hc]
  · intro x hx
    have h : ∃ x' ∈ S, phi x' = phi x := ⟨x, hx, rfl⟩
    have hx' : phi (Classical.choose h) = phi x := (Classical.choose_spec h).2
    have he : Classical.choose h = x := hinj (Classical.choose_spec h).1 hx hx'
    show (if h' : ∃ x' ∈ S, phi x' = phi x then Classical.choose h' else 0) = x
    rw [dif_pos h, he]

/-- **HOL `iso_list_sym`**（tame_list.hl:3328
`iso_list L L' /\ (set_of_list (MAP FST (flatten (SND L))) SUBSET
elements_of_list (FST L)) /\ (set_of_list (MAP SND (flatten (SND L))) SUBSET
elements_of_list (FST L)) ==> iso_list L' L`；载体 = 批 1 `IsoListSpine`，
两组 SUBSET 前提按逐点 ∈ 形平铺——诚实记账见头注）。 -/
theorem isoListSpineSym {L L' : fgraph ℕ} {N N' : List (List (ℕ × ℕ))}
    (h : IsoListSpine L L' N N')
    (h1 : ∀ p ∈ N.flatten, p.1 ∈ elementsOfList L)
    (h2 : ∀ p ∈ N.flatten, p.2 ∈ elementsOfList L) :
    IsoListSpine L' L N' N := by
  obtain ⟨phi, hinj, hL', hN'⟩ := h
  have himg : elementsOfList L' = phi '' elementsOfList L := by
    rw [hL']; exact elementsOfListMap L phi
  obtain ⟨phi', hinj', hinv⟩ := existsInverseOfInjOn
    (S := elementsOfList L) (T := elementsOfList L') hinj (fun y hy => by
      rw [himg] at hy
      rcases (Set.mem_image _ _ _).mp hy with ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy⟩)
  have hmemEl : ∀ (s : List ℕ) (x : ℕ), s ∈ L → x ∈ s → x ∈ elementsOfList L :=
    fun s x hs hx => List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨s, hs, hx⟩)
  refine ⟨phi', hinj', ?_, ?_⟩
  · rw [hL']
    have e : (L.map (List.map phi)).map (List.map phi')
        = L.map (List.map (phi' ∘ phi)) := by
      rw [List.map_map]
      refine List.map_congr_left (fun s _ => List.map_map)
    rw [e, List.map_congr_left (f := List.map (phi' ∘ phi)) (g := id)
      (fun s hs => by
        rw [List.map_congr_left (f := (phi' ∘ phi)) (g := id)
          (fun x hx => hinv x (hmemEl s x hs hx)), List.map_id]
        rfl),
      List.map_id]
  · rw [hN']
    have e : (N.map (fun s => s.map (fun u => (phi u.1, phi u.2)))).map
        (List.map (fun u => (phi' u.1, phi' u.2)))
        = N.map (List.map (fun u => (phi' (phi u.1), phi' (phi u.2)))) := by
      rw [List.map_map]
      refine List.map_congr_left (fun s _ => List.map_map)
    rw [e, List.map_congr_left
      (f := List.map (fun u => (phi' (phi u.1), phi' (phi u.2)))) (g := id)
      (fun s hs => by
        rw [List.map_congr_left (f := fun u => (phi' (phi u.1), phi' (phi u.2)))
          (g := id)
          (fun u hu => by
            have hu' : u ∈ N.flatten := List.mem_flatten.mpr ⟨s, hs, hu⟩
            have e1 := hinv u.1 (h1 u hu')
            have e2 := hinv u.2 (h2 u hu')
            show (phi' (phi u.1), phi' (phi u.2)) = u
            rw [e1, e2])]
        exact List.map_id s),
      List.map_id]

/-- **HOL `iso_list_all_uniq`**（tame_list.hl:3617
`iso_list (L,[]) (L',[]) /\ all uniq L ==> all uniq L'`；别名 UEYETNI :3641
同体不另立；`all uniq` ↦ 逐点 Nodup）。 -/
theorem isoListSpineAllUniq {L L' : fgraph ℕ} {N N' : List (List (ℕ × ℕ))}
    (h : IsoListSpine L L' N N') (hall : ∀ s ∈ L, s.Nodup) :
    ∀ s ∈ L', s.Nodup := by
  obtain ⟨phi, hinj, hL', -⟩ := h
  intro s hs
  rw [hL', List.mem_map] at hs
  obtain ⟨t, ht, hts⟩ := hs
  subst hts
  refine Kepler.Text.TameLp.la7_nodup_map_on (f := phi) (l := t) ?_ (hall t ht)
  intro u hu v hv huv
  exact injOn_elementsOfList_iff.mp hinj u (List.mem_flatten.mpr ⟨t, ht, hu⟩)
    v (List.mem_flatten.mpr ⟨t, ht, hv⟩) huv

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.indexToVertexListEnum
#print axioms Kepler.Text.TameSpine.isoListSpineSym
#print axioms Kepler.Text.TameSpine.eraseDupsMapEraseDups
#print axioms Kepler.Text.TameSpine.nextVerticesIndexf
-/

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.indexToVertexListEnum
#print axioms Kepler.Text.TameSpine.isoListSpineSym
#print axioms Kepler.Text.TameSpine.isoListSpineTrans
#print axioms Kepler.Text.TameSpine.eraseDupsMapEraseDups
#print axioms Kepler.Text.TameSpine.nextVerticesIndexf
-/
