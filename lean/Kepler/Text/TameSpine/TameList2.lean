/-
  Kepler.Text.TameSpine.TameList2 — B1 Tame_list 地基批 2：清单机器直译放量
  （tamespine-port-plan §4 批次表 B1 行，计划现位于 `docs/projects/tamespine-port-plan.md`；
  接续批 1 = TameList1.lean 的 S2/S6 重点件抽取，本批为「其余直译」的第 1 波）。

  立项：批次表 B1 行「tame_list.hl（前 2 批先抽 S2/S6 重点件……其余直译）」，
  14,428 行 / 650 定理 / 估 10-14 批。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  `text_formalization/tame/tame_list.hl:23-1466`——文件自述的 "general list
  processing results and small common lemmas" 块，即 indexf 定义（:1469）之前
  的全部前置清单机器；indexf/split_at/betwn 家族留待批 3+）：

  - Face/Graph 投影层 :72-212（faces/fgraph/setFinal/countVertices/makeFaceFinal）；
  - 基础 option/EL/filter :23-63、mem 基础 :157-193、flatten :221；
  - min_num/min_list/minimal_el 家族 :230-326/:803；
  - rotate 家族 :336-421/:526-544（HOL `rotate`/`rot` ↦ Mathlib `List.rotate`）；
  - `congs_rot` :431（scout §6-R8 的 `__cong` 商语义桥：HOL `?n. n <= LENGTH f1 /\
    f2 = rot n f1` ↦ Kepler.Graphs.cong 的 rotate 形）；
  - inj_on 家族 :459/:1147、insert_alt :422、nextElem/nextVertex :477-499；
  - `upt` 家族 :501-621/:1297（HOL `upt i j = [i..j-1]` 显式折算为 `Upt`）；
  - `replace` 三件 :546-598（Kepler.Graphs.replace 载体）；
  - zip·iota 家族 :635-801（`iota 0 k` ↦ `List.range k`，`rot 1`/`rotr 1` ↦
    `List.rotate 1`/`List.rotate (k-1)`）；
  - o_nth/map_flatten/zip_map/zip_swap/BIJ :832-937；
  - indexl 首现语义三件 :939/:1425-1466；
  - elements_of_list/list_of_darts 家族 :1066-1136、:1249；
  - filter/undup/replicate/last/next_el :1274-1417。

  批内分工记账（跳过件 NEEDS 注记）：
  - **TameLp la7 先行已覆盖**（ELLLNYZ lane 在账，本批零重复）：
    :948 prev_el_map（la7_prevEl_map）、:972 uniq_map（la7_nodup_map_on）、
    :988 indexl_map（la7_idxOf_map）、:1011 next_el_MEM_map（la7_nextEl_map）、
    :1037 map_list_pairs（la7_listPairs_map）、:1051 map_list_of_darts
    （la7_listOfDarts_map）、:1156 list_pairs2_rev（la7_listPairs_reverse）、
    :1218/:1229 list_pairs_rev/eq（la7_mem_listPairs_reverse）、
    :1239 list_of_darts_rev（la7_listOfDarts_reverse）、index_rot 的 Nodup 形
    （la7_idxOf_rotOne；本批补无 Nodup 首现语义一般形 :1453）。
  - **HOL 库内部同义词，Lean 无对应载体**（跳过，非内容件）：
    :53 filter_FILTER、:63 APPEND_cat、:305 minn_MIN、:600/:905 REVERSE_rev、
    :1389 rev0（HOL Seq 库与 list 库的换算，Lean 侧 List.* 即唯一载体）、
    :468 INJ_inj_on（INJ f s UNIV 即 inj_on f s）。
  - **NEEDS（载体在后续批成形）**：:518 RTranCl_REFL（RTranCl 关系层随 B5
    reduction 链立载体）、:822 uniq_perm_eq_map 与 :849 perm_eq_map_exists
    （perm_eq ↦ List.Perm 折算留待消费批）、:1138 f_list_ext_f_list
    （f_list_ext/res junk 层属 Sphere.res 语义桥，W0-adjacent）、
    :1249 list_of_darts_rev_uniq（其证明需 reverse-lods 的 nodup 迁移链：
    la7-iff 仅为单元素 mem 运输，nodup 需面级成对不交结构归纳，留待
    消费批与 la7-nodup 基建同波）。
  - **诚实收窄**：:832 o_nth 的 HOL 函数等式（`f o nth x0 x = nth (f x0) (map f x)`
    依赖 HOL nth 的 junk 约定）按 getD 同默认值逐点形收窄（两个默认元同取
    `f d0`，域内域外均恒等，无 junk 语义损失；Mathlib `List.getD_map` 逐字）；
    :1121 BIJ_IMAGE_darts_of_list 的 `good_list x` 前提在 HOL 证明体中亦未被
    消费（ONE_ONE_IMP_BIJ_IMAGE 只用单射性 + :1051 像方程），按原文携带、
    docstring 记账；:23 nth_EL、:33 the_some 的越界/部分性 junk 按
    getD/Option.getD 默认值约定吸收（scout §6-R5 家族）；
    :1309 undup_cat 的列表等式形在 Lean `List.eraseDups`（保首次出现）语义下
    不成立（HOL `undup` 保最后出现），按成员谓词形 `undupCat_mem` 收窄落地
    （两语义成员谓词一致）。

  红线遵守：本模块零 sorry、零既有文件触碰、零 git 写操作。
-/
import Kepler.Assembly
import Kepler.Text.TameLp
import Kepler.Text.Hypermap
import Kepler.Text.TameSpine.Keystone
import Kepler.Text.TameSpine.TameList1

namespace Kepler.Text.TameSpine

open Kepler.Assembly (listPairs nextEl listOfDarts GoodList)
open Kepler.Graphs (fgraph replace makeFaceFinal minimal min_list cong setFinal nextElem graph)
open Kepler.Text.TameLp (elementsOfList listOfElements)

/-! ### §1 Face/Graph 投影层（tame_list.hl:72-212）

HOL `Graph (face list) nat (face list list) (nat list)` 与 Lean `Kepler.Graphs.Graph`
字段一一对应（faces/countVertices/faceListAt/heights）；HOL `Face vs f` 的
`FST`/`SND` ↦ Lean `Face.vertices`/`Face.isFinal`（AFI Graph.thy 载体）。 -/

/-- HOL `fgraph` 函数（tame_list.hl:80 `fgraph (Graph f n a b) = MAP FST f`）的
Lean 载体：`fgraph` 在 Lean 是类型缩写 `List (List α)`，Graph→fgraph 的投影
函数按 `MAP FST` 语义立为 `facesVertexLists`。 -/
def facesVertexLists (g : Kepler.Graphs.Graph) : List (List Kepler.Graphs.Vertex) :=
  g.faces.map (fun f => f.vertices)

/-- HOL `faces_graph`（tame_list.hl:72 `faces (Graph fs n f h) = fs`）。 -/
theorem facesGraph (fs : List Kepler.Graphs.Face) (n : ℕ) (f : List (List Kepler.Graphs.Face)) (h : List ℕ) :
    (Kepler.Graphs.Graph.mk fs n f h).faces = fs := rfl

/-- HOL `fgraph_graph`（tame_list.hl:80 `fgraph (Graph f n a b) = MAP FST f`）。 -/
theorem fgraphGraphEq (f : List Kepler.Graphs.Face) (n : ℕ) (a : List (List Kepler.Graphs.Face)) (b : List ℕ) :
    facesVertexLists (Kepler.Graphs.Graph.mk f n a b) = f.map (fun F => F.vertices) := rfl

/-- HOL `fgraph_Faces`（tame_list.hl:184
`f IN Faces g ==> MEM (FST f) (fgraph g)`）。 -/
theorem fgraphFaces {g : Kepler.Graphs.Graph} {F : Kepler.Graphs.Face} (hF : F ∈ g.faces) :
    F.vertices ∈ facesVertexLists g :=
  List.mem_map_of_mem hF

/-- HOL `final_SND`（tame_list.hl:88 `SND (Face vs f) = if f = T then T else F`；
Bool 层恒等，Lean `Face.final = Face.isFinal`）。 -/
theorem finalSnd (vs : List Kepler.Graphs.Vertex) (b : Bool) : (Kepler.Graphs.Face.mk vs b).final = b := rfl

/-- HOL `type_face_SND`（tame_list.hl:97 `SND (Face vs f) = f`）。 -/
theorem typeFaceSnd (vs : List Kepler.Graphs.Vertex) (b : Bool) : (Kepler.Graphs.Face.mk vs b).isFinal = b := rfl

/-- HOL `vertices_face_FST`（tame_list.hl:105 `FST (Face vs f) = vs`）。 -/
theorem verticesFaceFst (vs : List Kepler.Graphs.Vertex) (b : Bool) : (Kepler.Graphs.Face.mk vs b).vertices = vs := rfl

/-- HOL `setFinal_ALT`（tame_list.hl:113 `setFinal f = Face (FST f) T`）。 -/
theorem setFinalAlt (f : Kepler.Graphs.Face) : setFinal f = Kepler.Graphs.Face.mk f.vertices true := rfl

/-- HOL `countVertices`（tame_list.hl:122 `countVertices (Graph fs n f h) = n`）。 -/
theorem countVerticesGraph (fs : List Kepler.Graphs.Face) (n : ℕ) (f : List (List Kepler.Graphs.Face)) (h : List ℕ) :
    (Kepler.Graphs.Graph.mk fs n f h).countVertices = n := rfl

/-- HOL `vertices_graph_alt`（tame_list.hl:130
`vertices_graph (Graph fs n f h) = upt 0 n`；`upt 0 n = [0..n-1]` ↦
`List.range n`，与批内 `upt0` 一致的折算）。 -/
theorem verticesGraphAlt (fs : List Kepler.Graphs.Face) (n : ℕ) (f : List (List Kepler.Graphs.Face)) (h : List ℕ) :
    (Kepler.Graphs.Graph.mk fs n f h).vertices = List.range n := rfl

/-- HOL `FACE_LIST_AT`（tame_list.hl:138 `faceListAt (Graph fs n f h) = f`）。 -/
theorem faceListAtGraph (fs : List Kepler.Graphs.Face) (n : ℕ) (f : List (List Kepler.Graphs.Face)) (h : List ℕ) :
    (Kepler.Graphs.Graph.mk fs n f h).faceListAt = f := rfl

/-- HOL `graph_ALT`（tame_list.hl:146：`graphl n` 的四字段显式形，
vs = upt 0 n = List.range n，Face 终态标记 T/F 与 Isabelle 载体一致）。 -/
theorem graphAlt (n : ℕ) : graph n =
    Kepler.Graphs.Graph.mk [Kepler.Graphs.Face.mk (List.range n) true, Kepler.Graphs.Face.mk (List.range n).reverse false] n
      (List.replicate n [Kepler.Graphs.Face.mk (List.range n) true, Kepler.Graphs.Face.mk (List.range n).reverse false])
      (List.replicate n 0) := rfl

/-- HOL `FST_setFinal`（tame_list.hl:195
`MAP FST (replace f [setFinal f] vs) = MAP FST vs`；
`replace` ↦ Kepler.Graphs.replace，`setFinal` 只改终态标记不动顶点表）。 -/
theorem fstSetFinal (f : Kepler.Graphs.Face) (vs : List Kepler.Graphs.Face) :
    (replace f [setFinal f] vs).map (fun F => F.vertices) = vs.map (fun F => F.vertices) := by
  induction vs with
  | nil => rfl
  | cons z zs ih =>
    show (if z == f then [setFinal f] ++ zs else z :: replace f [setFinal f] zs).map
      (fun F => F.vertices) = _
    by_cases hz : z = f
    · rw [if_pos (by simpa using hz)]
      simp [setFinalAlt, hz]
    · rw [if_neg (by simpa using hz)]
      simp only [List.map_cons]
      exact congrArg _ ih

/-- HOL `fgraph_makeFaceFinal`（tame_list.hl:212
`fgraph (makeFaceFinal f g) = fgraph g`；makeFaceFinal ↦ Kepler.Graphs.makeFaceFinal）。 -/
theorem fgraphMakeFaceFinal (f : Kepler.Graphs.Face) (g : Kepler.Graphs.Graph) :
    facesVertexLists (makeFaceFinal f g) = facesVertexLists g := by
  show (replace f [setFinal f] g.faces).map (fun F => F.vertices) = _
  exact fstSetFinal f g.faces

/-! ### §2 option/EL/filter 基础（tame_list.hl:23-63） -/

/-- HOL `nth_EL` 前半（tame_list.hl:23 `EL 0 (x::xs) = x`）。 -/
theorem nthElConsZero (x : α) (xs : List α) (d : α) : (x :: xs).getD 0 d = x := rfl

/-- HOL `nth_EL` 后半（tame_list.hl:23 `EL (SUC k) (x::xs) = EL k xs`）的
getD 形（HOL EL 越界的 junk 约定按 getD 默认值吸收，scout §6-R5）。 -/
theorem nthElConsSucc (x : α) (xs : List α) (n : ℕ) (d : α) :
    (x :: xs).getD (n + 1) d = xs.getD n d := by
  by_cases h : n < xs.length
  · have h1 : n + 1 < (x :: xs).length := by simpa using Nat.succ_lt_succ h
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h, List.getElem_cons_succ]
  · have h1 : (x :: xs).length ≤ n + 1 := by simpa using Nat.succ_le_succ (Nat.ge_of_not_lt h)
    have h2 : xs.length ≤ n := Nat.ge_of_not_lt h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none h2]

/-- HOL `the_some`（tame_list.hl:33 `the (SOME x) = x`；`the` 的部分性按
`Option.getD` 默认值约定吸收——默认元任意时等式仍真）。 -/
theorem theSome (x d : α) : Option.getD (Option.some x) d = x := rfl

/-- HOL `filter_rec`（tame_list.hl:44 `filter` 在 nil/cons 的展开方程；
Lean `List.filter` 即同一函数，方程为 Mathlib 标准件）。 -/
theorem filterRec (p : α → Bool) :
    List.filter p [] = [] ∧
      ∀ x xs, List.filter p (x :: xs) = if p x then x :: List.filter p xs else List.filter p xs := by
  refine ⟨rfl, fun x xs => ?_⟩
  rw [List.filter_cons]

/-- HOL `INSERT_alt`（tame_list.hl:422 `INSERT a B = {x | x = a \/ x IN B}`）。 -/
theorem insertAlt (a : α) (B : Set α) : insert a B = {x | x = a ∨ x ∈ B} :=
  Set.insert_def a B

/-! ### §3 mem 基础（tame_list.hl:157-193） -/

/-- HOL `MEMf_MAP`（tame_list.hl:157 `MEM x u ==> MEM (f x) (MAP f u)`）。 -/
theorem memfMap {f : α → β} {x : α} {u : List α} (h : x ∈ u) : f x ∈ u.map f :=
  List.mem_map_of_mem h

/-- HOL `MEM_HD`（tame_list.hl:165 `~(xs = []) ==> MEM (HD xs) xs`）。 -/
theorem memHd {α : Type*} [Inhabited α] {xs : List α} (h : xs ≠ []) : xs.head! ∈ xs :=
  List.head!_mem_self h

/-- HOL `MEM_EQ_NIL`（tame_list.hl:176 `s = [] <=> (!x. ~MEM x s)`）。 -/
theorem memEqNil (s : List α) : s = [] ↔ ∀ x, x ∉ s := by
  constructor
  · intro h x hx
    exact List.not_mem_nil (h ▸ hx)
  · intro h
    cases s with
    | nil => rfl
    | cons a t => exact absurd (h a List.mem_cons_self) (by simp)

/-! ### §4 flatten（tame_list.hl:221） -/

/-- HOL `concat_flatten`（tame_list.hl:221 `flatten` 在 nil/cons 的展开方程）。 -/
theorem concatFlatten (x : List α) (xs : List (List α)) :
    ([] : List (List α)).flatten = [] ∧ (x :: xs).flatten = x ++ xs.flatten :=
  ⟨rfl, List.flatten_cons ..⟩

/-! ### §5 min_num / min_list / minimal_el（tame_list.hl:230-326/:803）

HOL `min_num X`（num 集的最小元）↦ Lean `Finset.min'`（空集部分性由
`Nonempty` 证书承载，语义同构）。`min_list` ↦ Kepler.Graphs.min_list
（Isabelle AFP 同源载体），`minimal_el` ↦ Kepler.Graphs.minimal。 -/

/-- HOL `min_num_single`（tame_list.hl:230 `min_num {x} = x`）。 -/
theorem minNumSingle (x : ℕ) : ({x} : Finset ℕ).min' (Finset.singleton_nonempty x) = x :=
  Finset.min'_singleton x

/-- HOL `min_num_in`（tame_list.hl:242 `~(X = {}) ==> min_num X IN X`）。 -/
theorem minNumIn {X : Finset ℕ} (h : X.Nonempty) : X.min' h ∈ X :=
  Finset.min'_mem _ h

/-- HOL `min_num_le`（tame_list.hl:252 `c IN X ==> min_num X <= c`）。 -/
theorem minNumLe {X : Finset ℕ} {c : ℕ} (hc : c ∈ X) : X.min' (⟨c, hc⟩) ≤ c :=
  Finset.min'_le X c hc

/-- HOL `min_num_unique`（tame_list.hl:261
`c IN X /\ (!c'. c' IN X ==> c <= c') ==> min_num X = c`）。 -/
theorem minNumUnique {X : Finset ℕ} {c : ℕ} (hc : c ∈ X) (h : ∀ c' ∈ X, c ≤ c') :
    X.min' (⟨c, hc⟩) = c :=
  le_antisymm (Finset.min'_le X c hc) (h _ (Finset.min'_mem X ⟨c, hc⟩))

/-- HOL `min_num_insert`（tame_list.hl:276
`~(X = {}) ==> min_num (x INSERT X) = MIN x (min_num X)`）。 -/
theorem minNumInsert {X : Finset ℕ} {x : ℕ} (h : X.Nonempty) :
    (insert x X).min' (Finset.insert_nonempty x X) = min x (X.min' h) := by
  refine minNumUnique ?_ ?_
  · by_cases hle : x ≤ X.min' h
    · rw [min_eq_left hle]; exact Finset.mem_insert_self x X
    · rw [min_eq_right (le_of_lt (not_le.mp hle))]
      exact Finset.mem_insert_of_mem (Finset.min'_mem X h)
  · intro c' hc'
    by_cases hle : x ≤ X.min' h
    · rw [min_eq_left hle]
      rcases Finset.mem_insert.mp hc' with rfl | hc'
      · exact le_refl _
      · exact le_trans hle (Finset.min'_le X c' hc')
    · rw [min_eq_right (le_of_lt (not_le.mp hle))]
      rcases Finset.mem_insert.mp hc' with rfl | hc'
      · exact le_of_lt (not_le.mp hle)
      · exact Finset.min'_le X c' hc'

/-- HOL `min_list_cons`（tame_list.hl:315
`min_list (x :: xs) = if xs = [] then x else MIN x (min_list xs)`；
即 Kepler.Graphs.min_list 的定义方程，`isEmpty` 换写）。 -/
theorem minListCons (x : ℕ) (xs : List ℕ) :
    min_list (x :: xs) = if xs = [] then x else min x (min_list xs) := by
  by_cases h : xs = [] <;> simp [min_list, h]

/-- HOL `mem_minimal_el`（tame_list.hl:803
`~(xs = []) ==> MEM (minimal_el f xs) xs`）——本体 = ListAuxLemmas
`minimal_in_set`（Isabelle 同源载体），本件为桥形。 -/
theorem memMinimalEl {α : Type*} [Inhabited α] (f : α → ℕ) {xs : List α} (h : xs ≠ []) :
    minimal f xs ∈ xs :=
  Kepler.Graphs.minimal_in_set f h

/-- HOL `ITER_o`（tame_list.hl:328 `ITER 0 f = I /\ ITER (SUC n) f = f o ITER n f`；
HOL `ITER` ↦ Lean `Function.iterate`，方程为 Mathlib 定义件）。 -/
theorem iterateSpine {α : Type*} (f : α → α) :
    f^[0] = id ∧ ∀ n : ℕ, f^[n + 1] = f ∘ f^[n] :=
  ⟨Function.iterate_zero _, fun n => Function.iterate_succ' f n⟩

/-! ### §6 rotate 家族（tame_list.hl:336-421/:526-544）

HOL `rotate n = ITER n rotate1`（Seq 库）与 `rot n x = drop n x ++ take n x`
在 `n ≤ LENGTH x` 时重合（rotate_rot :355）；Lean 侧统一载体为 Mathlib
`List.rotate`（其定义即 `drop (n % len) ++ take (n % len)`），本节把 HOL
rotate 方程逐条运输为 `List.rotate` API 桥件。 -/

/-- HOL `rotate_add`（tame_list.hl:374 `rotate (n+m) x = rotate n (rotate m x)`）。 -/
theorem rotateSpineAdd (l : List α) (n m : ℕ) : l.rotate (n + m) = (l.rotate n).rotate m :=
  (List.rotate_rotate l n m).symm

/-- HOL `rotate_nil`（tame_list.hl:382 `rotate n [] = []`）。 -/
theorem rotateSpineNil (n : ℕ) : ([] : List α).rotate n = [] := rfl

/-- HOL `rotate_periodic`（tame_list.hl:392
`rotate (n + LENGTH x) x = rotate n x`）。 -/
theorem rotateSpinePeriodic (l : List α) (n : ℕ) :
    l.rotate (n + l.length) = l.rotate n := by
  have harith : (n + l.length) % l.length = n % l.length := by
    rw [Nat.add_comm, ← Nat.mod_add_mod, Nat.mod_self, Nat.zero_add]
  rw [← List.rotate_mod l (n + l.length), ← List.rotate_mod l n]
  exact congrArg (fun m => l.rotate m) harith

/-- HOL `rotate_mod`（tame_list.hl:405 `rotate n x = rotate (n MOD LENGTH x) x`）。 -/
theorem rotateSpineMod (l : List α) (n : ℕ) : l.rotate n = l.rotate (n % l.length) :=
  (List.rotate_mod l n).symm

/-- HOL `rotate_0`（tame_list.hl:526 `rotate 0 x = x`）。 -/
theorem rotateSpineZero (l : List α) : l.rotate 0 = l := List.rotate_zero l

/-- HOL `rotate_eq_nil`（tame_list.hl:534 `rotate n x = [] <=> x = []`）。 -/
theorem rotateSpineEqNil {l : List α} {n : ℕ} : l.rotate n = [] ↔ l = [] :=
  List.rotate_eq_nil_iff

/-- HOL `rotate_rot`（tame_list.hl:355 `n <= LENGTH x ==> rotate n x = rot n x`；
HOL `rot` 即 `drop ++ take`，与 Mathlib rotate 的 `n ≤ length` 折算式重合）。 -/
theorem rotateSpineRot {l : List α} {n : ℕ} (h : n ≤ l.length) :
    l.rotate n = l.drop n ++ l.take n :=
  List.rotate_eq_drop_append_take h

/-- HOL `rotate_rotate1`+`rotate1_rot1`（tame_list.hl:336/:344：rotate 1 =
rotate1 = rot 1 的合成桥；与 TameLp `la7RotOne` 定义方程一致）。 -/
theorem rotateSpineOne (l : List α) : l.rotate 1 = l.drop 1 ++ l.take 1 := by
  by_cases hl : l = []
  · subst hl; rfl
  · have h0 : 0 < l.length := List.length_pos_iff.mpr (by simp [hl])
    exact rotateSpineRot (by omega)

/-- HOL `list_pairs` 与 `rotate 1` 的关系（:344 `rotate1 = rot 1` 在
list_pairs 载体上的推论；批内 zip·iota 家族的共用形）。 -/
theorem listPairsEqZipRotate (l : List α) : listPairs l = l.zip (l.rotate 1) := by
  show l.zip (l.drop 1 ++ l.take 1) = _
  rw [← rotateSpineOne]

/-! ### §7 congs_rot（tame_list.hl:431）

scout §6-R8 的 `__cong` 商语义桥：HOL `__cong f1 f2 <=> ?n. n <= LENGTH f1 /\
f2 = rot n f1`；Lean 载体 = Kepler.Graphs.cong（`∃ n, ys = xs.rotate n`），
`n ≤ length` 一侧由 `rotate_mod` 吸收（n 可约去模长）。 -/

/-- HOL `congs_rot`（tame_list.hl:431）。 -/
theorem congsRot {f1 f2 : List α} : cong f1 f2 ↔ ∃ n, n ≤ f1.length ∧ f2 = f1.rotate n := by
  constructor
  · rintro ⟨n, hn⟩
    by_cases h0 : f1.length = 0
    · refine ⟨0, by omega, ?_⟩
      rw [hn, List.length_eq_zero_iff.mp h0]
      simp
    · exact ⟨n % f1.length, le_of_lt (Nat.mod_lt _ (by omega)), by rw [hn, List.rotate_mod]⟩
  · rintro ⟨n, -, rfl⟩
    exact ⟨n, rfl⟩

/-! ### §8 inj_on 家族（tame_list.hl:459/:1147） -/

/-- HOL `inj_on_ALT`（tame_list.hl:459
`inj_on f A <=> !x. x IN A ==> !y. y IN A ==> f x = f y ==> x = y`；
`Set.InjOn` 的定义形重述）。 -/
theorem injOnAlt {A : Set α} {f : α → β} :
    Set.InjOn f A ↔ ∀ x ∈ A, ∀ y ∈ A, f x = f y → x = y := by
  constructor
  · intro h x hx y hy hxy
    exact h hx hy hxy
  · intro h
    exact fun a ha b hb hab => h a ha b hb hab

/-- HOL `inj_on_subset`（tame_list.hl:1147
`inj_on phi U /\ V SUBSET U ==> inj_on phi V`）。 -/
theorem injOnSubsetSpine {U V : Set α} {f : α → β} (h : Set.InjOn f U) (hsub : V ⊆ U) :
    Set.InjOn f V :=
  h.mono hsub

/-! ### §9 nextElem / nextVertex（tame_list.hl:477-499）

载体 = Kepler.Graphs.nextElem/Face.nextVertex（Isabelle Graph.thy 同源）。 -/

/-- HOL `nextElem_ALT`（tame_list.hl:477 `nextElem` 在 nil/cons 的展开方程；
cons 支的 `HD as`（带非空守卫）按 match（`[]` 归 `b`）折算——载体
Kepler.Graphs.nextElem 本就 BEq 化（Graph.lean:60），第二支即 GraphProps
`nextElem_cons` 的逐字桥；守卫版 junk 缺省取 `b`（`headD b`）。 -/
theorem nextElemAlt {α : Type*} [BEq α] (a : α) (as : List α) (b x : α) :
    nextElem [] b x = b ∧
      nextElem (a :: as) b x =
        if x == a then (match as with | [] => b | a' :: _ => a') else nextElem as b x :=
  ⟨rfl, Kepler.Graphs.nextElem_cons a as b x⟩

/-- HOL `nextElem_ALT` 的守卫版（tame_list.hl:477 cons 支 `if as = []` 分岔
显式化；`HD as` 的非空守卫由 match 保证）。 -/
theorem nextElemAltGuard {α : Type*} [BEq α] (a : α) (as : List α) (b x : α) :
    nextElem [] b x = b ∧
      nextElem (a :: as) b x =
        if x == a then (if as = [] then b else as.headD b) else nextElem as b x := by
  refine ⟨rfl, ?_⟩
  simp only [Kepler.Graphs.nextElem_cons]
  by_cases hxa : (x == a) = true
  · simp only [if_pos hxa]
    cases as <;> rfl
  · simp only [if_neg hxa]

/-- HOL `nextVertex_ALT`（tame_list.hl:491
`nextVertex f = nextElem vs (HD vs)`，vs = 顶点表；即 Face.nextVertex
定义方程的逐字折算）。 -/
theorem nextVertexAlt (f : Kepler.Graphs.Face) (v : Kepler.Graphs.Vertex) :
    f.nextVertex v = nextElem f.vertices f.vertices.head! v := rfl

/-! ### §10 upt 家族（tame_list.hl:501-621/:1297）

HOL `upt i j = [i, i+1, .., j-1]`（`i > j` 时为空）。折算为显式 `Upt`：
`if i ≤ j then (range (j - i)).map (· + i) else []`（与 `List.range` 偏移
携带一体；AFI Graph.thy 的 `vertices = upt 0 n` 已按 `List.range n` 落地）。 -/

/-- HOL `upt`（tame_list 载体函数，tame_list.hl:501-614/:1297 使用）。 -/
def Upt (i j : ℕ) : List ℕ :=
  if i ≤ j then (List.range (j - i)).map (fun x => i + x) else []

/-- HOL `upt_rec`（tame_list.hl:501
`upt i 0 = [] /\ upt i (SUC j) = if i <= j then upt i j ++ [j] else []`）。 -/
theorem uptRec (i : ℕ) :
    Upt i 0 = [] ∧ ∀ j : ℕ, Upt i (j + 1) = if i ≤ j then Upt i j ++ [j] else [] := by
  refine ⟨by unfold Upt; split <;> simp, fun j => ?_⟩
  by_cases h : i ≤ j
  · have hji : j + 1 - i = (j - i) + 1 := by omega
    simp only [Upt, if_pos (show i ≤ j + 1 by omega), if_pos h, hji,
      List.range_succ, List.map_append, List.map_cons, List.map_nil]
    exact congrArg (fun x => List.map (fun x => i + x) (List.range (j - i)) ++ [x])
      (by omega : i + (j - i) = j)
  · by_cases h1 : i ≤ j + 1
    · have hj1 : j + 1 - i = 0 := by omega
      simp only [Upt, if_pos h1, if_neg h, hj1, List.range_zero, List.map_nil]
    · simp only [Upt, if_neg h1, if_neg h]

/-- HOL `upt0`（tame_list.hl:614 `upt 0 i = iota 0 i`；`iota 0 i` ↦
`List.range i`）。 -/
theorem upt0 (i : ℕ) : Upt 0 i = List.range i := by
  unfold Upt
  rw [if_pos (Nat.zero_le i)]
  simp

/-- HOL `CARD_upt`（tame_list.hl:1297 `CARD (set_of_list (upt 0 n)) = n`；
`set_of_list` ↦ `List.toFinset`）。 -/
theorem cardUpt (n : ℕ) : (Upt 0 n).toFinset.card = n := by
  rw [upt0, List.toFinset_range, Finset.card_range]

/-! ### §11 replace 三件（tame_list.hl:546-598）

载体 = Kepler.Graphs.replace（`replace x ys zs` 把 `zs` 中首个 `x` 换成
`ys`，与 HOL `replace f xs g` 参数逐位对应）。 -/

/-- HOL `MEM_replace`（tame_list.hl:546
`MEM x (replace f xs g) ==> MEM x g \/ (MEM f g /\ MEM x xs)`）。 -/
theorem memReplace {α : Type*} [BEq α] [LawfulBEq α] {x f : α} {xs : List α} :
    ∀ g : List α, x ∈ replace f xs g → x ∈ g ∨ (f ∈ g ∧ x ∈ xs) := by
  intro g
  induction g with
  | nil => intro hm; cases hm
  | cons z zs ih =>
    intro hm
    rw [show replace f xs (z :: zs)
        = (if z == f then xs ++ zs else z :: replace f xs zs) from rfl] at hm
    by_cases hz : z = f
    · rw [if_pos (by simpa using hz)] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inr ⟨by rw [← hz]; exact List.mem_cons_self, hm⟩
      · exact Or.inl (List.mem_cons_of_mem _ hm)
    · rw [if_neg (by simpa using hz)] at hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inl List.mem_cons_self
      · rcases ih hm with h' | ⟨h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- HOL `MEM2_replace`（tame_list.hl:566
`MEM f g /\ MEM x xs ==> MEM x (replace f xs g)`）。 -/
theorem memReplaceOfMem {α : Type*} [BEq α] [LawfulBEq α] {x f : α} {xs g : List α}
    (hf : f ∈ g) (hx : x ∈ xs) : x ∈ replace f xs g := by
  induction g with
  | nil => cases hf
  | cons z zs ih =>
    show x ∈ (if z == f then xs ++ zs else z :: replace f xs zs)
    by_cases hz : z = f
    · rw [if_pos (by simpa using hz)]
      exact List.mem_append.mpr (Or.inl hx)
    · rw [if_neg (by simpa using hz)]
      rcases List.mem_cons.mp hf with rfl | hf'
      · exact absurd rfl hz
      · exact List.mem_cons_of_mem _ (ih hf')

/-- HOL `MEM3_replace`（tame_list.hl:583
`~(x = f) /\ MEM x g ==> MEM x (replace f xs g)`）。 -/
theorem memReplaceOfNe {α : Type*} [BEq α] [LawfulBEq α] {x f : α} {xs g : List α}
    (hne : x ≠ f) (hx : x ∈ g) : x ∈ replace f xs g := by
  induction g with
  | nil => cases hx
  | cons z zs ih =>
    show x ∈ (if z == f then xs ++ zs else z :: replace f xs zs)
    by_cases hz : z = f
    · rw [if_pos (by simpa using hz)]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact absurd hz hne
      · exact List.mem_append.mpr (Or.inr hx')
    · rw [if_neg (by simpa using hz)]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hx')

/-! ### §12 zip·iota 家族（tame_list.hl:635-801）

`iota 0 k` ↦ `List.range k`；`rot 1` ↦ `List.rotate 1`；`rotr 1`（右旋）↦
`List.rotate (k-1)`。这一族是 hypermap_of_list 节点/边枚举的算术骨架
（AQ12/reduction 消费）。 -/

/-- 私有辅助：`zip (range k) (rotate n (range k))` 的长度（`zip`/`rotate` 长度
方程合成，iota 家族共用）。 -/
private theorem lenZipRotRange (k n : ℕ) :
    ((List.range k).zip ((List.range k).rotate n)).length = k := by
  rw [List.length_zip]
  simp

/-- 私有辅助：`rotate` 的 getElem 值方程，模长已按 `(range k).length = k`
归一（`simp only` 处理依赖下标的证明项）。 -/
private theorem getElemRotateRange {k n i : ℕ} (h2 : i < ((List.range k).rotate n).length)
    (hp : (i + n) % k < (List.range k).length) :
    ((List.range k).rotate n)[i]'h2 = (List.range k)[(i + n) % k]'hp := by
  rw [List.getElem_rotate]
  simp only [List.length_range]

/-- 私有辅助：`zip (range k) (rotate n (range k))` 的 getD 逐点方程
（`getElem?_zip_eq_some` + `getElem?_eq_some_getElem_iff` 桥接，无裸索引孔，
iota 家族共用）。 -/
private theorem getDZipRotRange {k n i : ℕ} (h : i < k) (d : ℕ × ℕ) :
    ((List.range k).zip ((List.range k).rotate n)).getD i d
      = ((List.range k).getD i d.1, (List.range k).getD ((i + n) % k) d.2) := by
  have hrl : (List.range k).length = k := List.length_range
  have h1 : i < (List.range k).length := by rw [hrl]; exact h
  have h2 : i < ((List.range k).rotate n).length := by
    rw [List.length_rotate, hrl]; exact h
  have hi : i < ((List.range k).zip ((List.range k).rotate n)).length := by
    rw [lenZipRotRange]; exact h
  have hmod : (i + n) % k < (List.range k).length := by
    rw [hrl]; exact Nat.mod_lt _ (by omega)
  have hrot := getElemRotateRange h2 hmod
  have hsome : ((List.range k).zip ((List.range k).rotate n))[i]?
      = some (((List.range k).zip ((List.range k).rotate n))[i]'hi) :=
    (List.getElem?_eq_some_getElem_iff hi).mpr trivial
  have hq : ((List.range k).zip ((List.range k).rotate n))[i]?
      = some (((List.range k)[i]'h1, ((List.range k).rotate n)[i]'h2)) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨(List.getElem?_eq_some_getElem_iff h1).mpr trivial,
      (List.getElem?_eq_some_getElem_iff h2).mpr trivial⟩
  rw [hrot] at hq
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ h1,
    List.getD_eq_getElem _ _ hmod]
  exact (Option.some.inj (hq.symm.trans hsome)).symm

/-- HOL `nth_iota_nod`（tame_list.hl:635 `i < k ==> nth x (iota 0 k) i = i`；
越界默认值按 getD 约定吸收）。 -/
theorem nthRangeOfLt {k i : ℕ} {d : ℕ} (h : i < k) : (List.range k).getD i d = i := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_range]; exact h)]
  exact List.getElem_range (by rw [List.length_range]; exact h)

/-- HOL `nth_zip_iota0`（tame_list.hl:649
`i' + 1 = k ==> nth (x,y) (zip (iota 0 k) (rot 1 (iota 0 k))) i' = (i', 0)`）。 -/
theorem nthZipIota0 {k x y i' : ℕ} (h : i' + 1 = k) :
    ((List.range k).zip ((List.range k).rotate 1)).getD i' (x, y) = (i', 0) := by
  have hik : i' < k := by omega
  rw [getDZipRotRange hik, nthRangeOfLt hik]
  have hmod : (i' + 1) % k = 0 := by rw [← h, Nat.mod_self]
  rw [hmod, nthRangeOfLt (by omega)]

/-- HOL `nth_zipr_iota0`（tame_list.hl:669
`0 < k ==> nth (x,y) (zip (iota 0 k) (rotr 1 (iota 0 k))) 0 = (0, k-1)`）。 -/
theorem nthZiprIota0 {k x y : ℕ} (hk : 0 < k) :
    ((List.range k).zip ((List.range k).rotate (k - 1))).getD 0 (x, y) = (0, k - 1) := by
  rw [getDZipRotRange hk, nthRangeOfLt hk]
  have hmod : (0 + (k - 1)) % k = k - 1 := by
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hmod, nthRangeOfLt (by omega)]

/-- HOL `nth_zip_iota`（tame_list.hl:687
`i' + 1 < k ==> nth (x,y) (zip (iota 0 k) (rot 1 (iota 0 k))) i' = (i', i'+1)`）。 -/
theorem nthZipIota {k x y i' : ℕ} (h : i' + 1 < k) :
    ((List.range k).zip ((List.range k).rotate 1)).getD i' (x, y) = (i', i' + 1) := by
  have hik : i' < k := by omega
  rw [getDZipRotRange hik, nthRangeOfLt hik]
  have hmod : (i' + 1) % k = i' + 1 := Nat.mod_eq_of_lt h
  rw [hmod, nthRangeOfLt h]

/-- HOL `nth_zipr_iota`（tame_list.hl:707
`0 < i' /\ i' < k ==> nth (x,y) (zip (iota 0 k) (rotr 1 (iota 0 k))) i'
= (i', i'-1)`）。 -/
theorem nthZiprIota {k x y i' : ℕ} (h0 : 0 < i') (hk : i' < k) :
    ((List.range k).zip ((List.range k).rotate (k - 1))).getD i' (x, y) = (i', i' - 1) := by
  rw [getDZipRotRange hk, nthRangeOfLt hk]
  have hmod : (i' + (k - 1)) % k = i' - 1 := by
    have he : i' + (k - 1) = (i' - 1) + k := by omega
    rw [he, ← Nat.add_mod_mod, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega)]
  rw [hmod, nthRangeOfLt (by omega)]

/-- HOL `list_pairs_iota`（tame_list.hl:727
`MEM (i,j) (list_pairs (iota 0 k)) <=>
((i+1 < k /\ j = i+1) \/ (i+1 = k /\ j = 0))`）。 -/
theorem memListPairsIota {i j k : ℕ} :
    (i, j) ∈ listPairs (List.range k) ↔
      (i + 1 < k ∧ j = i + 1) ∨ (i + 1 = k ∧ j = 0) := by
  constructor
  · intro h
    rw [listPairsEqZipRotate] at h
    obtain ⟨i', hi', hz⟩ := List.mem_iff_getElem.mp h
    have hik : i' < k := by rw [← lenZipRotRange k 1]; exact hi'
    have hilt : i' < (List.range k).length := by rw [List.length_range]; exact hik
    have h2 : i' < ((List.range k).rotate 1).length := by
      rw [List.length_rotate, List.length_range]; exact hik
    have hq : ((List.range k).zip ((List.range k).rotate 1))[i']? = some (i, j) :=
      List.getElem?_eq_some_iff.mpr ⟨hi', hz⟩
    rw [List.getElem?_zip_eq_some] at hq
    obtain ⟨hq1, hq2⟩ := hq
    have hr : ((List.range k).rotate 1)[i']?
        = ((List.range k)[(i' + 1) % (List.range k).length]?) :=
      List.getElem?_rotate hilt
    rw [hr] at hq2
    rw [List.length_range] at hq2
    rcases Nat.lt_or_ge (i' + 1) k with hk | hk
    · have hp : i' + 1 < (List.range k).length := by rw [List.length_range]; omega
      rw [Nat.mod_eq_of_lt hk] at hq2
      have e1 : (List.range k)[i']? = some i' :=
        List.getElem?_eq_some_iff.mpr ⟨hilt, List.getElem_range hilt⟩
      have e2 : (List.range k)[i' + 1]? = some (i' + 1) :=
        List.getElem?_eq_some_iff.mpr ⟨hp, List.getElem_range hp⟩
      rw [e1] at hq1
      rw [e2] at hq2
      have hii : i' = i := Option.some.inj hq1
      have hj : i' + 1 = j := Option.some.inj hq2
      exact Or.inl ⟨by omega, by omega⟩
    · have he : i' + 1 = k := by omega
      rw [he, Nat.mod_self] at hq2
      have e0 : (List.range k)[0]? = some 0 := by
        have hp : 0 < (List.range k).length := by rw [List.length_range]; omega
        exact List.getElem?_eq_some_iff.mpr ⟨hp, List.getElem_range hp⟩
      have e1 : (List.range k)[i']? = some i' :=
        List.getElem?_eq_some_iff.mpr ⟨hilt, List.getElem_range hilt⟩
      rw [e0] at hq2
      rw [e1] at hq1
      have hii : i' = i := Option.some.inj hq1
      have h0j : 0 = j := Option.some.inj hq2
      exact Or.inr ⟨by omega, by omega⟩

  · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩)
    · have hik : i < k := by omega
      have h1' : i < (List.range k).length := by rw [List.length_range]; exact hik
      have h2' : i < ((List.range k).rotate 1).length := by
        rw [List.length_rotate, List.length_range]; exact hik
      have hp : i + 1 < (List.range k).length := by rw [List.length_range]; omega
      have hw : ((List.range k).zip ((List.range k).rotate 1))[i]? = some (i, i + 1) := by
        rw [List.getElem?_zip_eq_some]
        refine ⟨List.getElem?_eq_some_iff.mpr ⟨h1', List.getElem_range h1'⟩, ?_⟩
        have e1 : ((List.range k).rotate 1)[i]?
            = ((List.range k)[(i + 1) % (List.range k).length]?) :=
          List.getElem?_rotate h1'
        rw [e1, List.length_range, Nat.mod_eq_of_lt h1]
        exact List.getElem?_eq_some_iff.mpr ⟨hp, List.getElem_range hp⟩
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hw
      rw [listPairsEqZipRotate]
      exact List.mem_iff_getElem.mpr ⟨i, hlt, heq⟩
    · have hk : 0 < k := by omega
      have hik : i < k := by omega
      have h1' : i < (List.range k).length := by rw [List.length_range]; exact hik
      have h2' : i < ((List.range k).rotate 1).length := by
        rw [List.length_rotate, List.length_range]; exact hik
      have hw : ((List.range k).zip ((List.range k).rotate 1))[i]? = some (i, 0) := by
        rw [List.getElem?_zip_eq_some]
        refine ⟨List.getElem?_eq_some_iff.mpr ⟨h1', List.getElem_range h1'⟩, ?_⟩
        have e1 : ((List.range k).rotate 1)[i]?
            = ((List.range k)[(i + 1) % (List.range k).length]?) :=
          List.getElem?_rotate h1'
        rw [e1, List.length_range, h1, Nat.mod_self]
        have hp : 0 < (List.range k).length := by rw [List.length_range]; exact hk
        exact List.getElem?_eq_some_iff.mpr ⟨hp, List.getElem_range hp⟩
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hw
      rw [listPairsEqZipRotate]
      exact List.mem_iff_getElem.mpr ⟨i, hlt, heq⟩

/-- HOL `list_pairs_rev_iota`（tame_list.hl:764
`0 < k ==> MEM (i,j) (list_pairs (rev (iota 0 k))) <=>
((i = 0 /\ j = k-1) \/ (0 < i /\ i < k /\ j = i-1))`）——经 TameLp
`la7_mem_listPairs_reverse`（:1229）折到 `memListPairsIota`。 -/
theorem memListPairsRevIota {i j k : ℕ} (hk : 0 < k) :
    (i, j) ∈ listPairs (List.range k).reverse ↔
      (i = 0 ∧ j = k - 1) ∨ (0 < i ∧ i < k ∧ j = i - 1) := by
  rw [TameLp.la7_mem_listPairs_reverse]
  show (j, i) ∈ listPairs (List.range k) ↔
    (i = 0 ∧ j = k - 1) ∨ (0 < i ∧ i < k ∧ j = i - 1)
  rw [memListPairsIota]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨by omega, by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩

/-! ### §13 o_nth / map_flatten / zip / BIJ（tame_list.hl:832-937） -/

/-- HOL `o_nth`（tame_list.hl:832 `f o nth x0 x = nth (f x0) (map f x)`）的
getD 逐点形：HOL 函数等式的 junk 语义按「两侧同默认元 `f d0`」收窄，
域内由 `List.getElem_map` 搬运、域外两同为默认元——本体即 Mathlib
`List.getD_map` 的逐字特例。 -/
theorem oNth {f : α → β} {l : List α} {d0 : α} {i : ℕ} :
    (l.map f).getD i (f d0) = f (l.getD i d0) :=
  List.getD_map ..

/-- HOL `MAP_flatten`（tame_list.hl:873
`MAP f (flatten x) = flatten (MAP (MAP f) x)`）。 -/
theorem mapFlattenSpine {f : α → β} (l : List (List α)) :
    l.flatten.map f = (l.map (List.map f)).flatten :=
  List.map_flatten ..

/-- HOL `zip_map`（tame_list.hl:882
`MAP (\u. f (FST u), g (SND u)) (zip x y) = zip (MAP f x) (MAP g y)`）。 -/
theorem zipMapSpine {f : α → γ} {g : β → δ} (l₁ : List α) (l₂ : List β) :
    (l₁.zip l₂).map (fun u => (f u.1, g u.2)) = (l₁.map f).zip (l₂.map g) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> rfl
  | cons a l₁ ih =>
    cases l₂ with
    | nil => rfl
    | cons b l₂ => simp only [List.zip_cons_cons, List.map_cons]; exact congrArg _ (ih l₂)

/-- HOL `ONE_ONE_IMP_BIJ_IMAGE`（tame_list.hl:892
`(!x y. x IN S /\ y IN S /\ f x = f y ==> x = y) ==> BIJ f S (IMAGE f S)`）。 -/
theorem oneOneImpBijImage {S : Set α} {f : α → β}
    (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) : Set.BijOn f S (f '' S) :=
  Set.InjOn.bijOn_image h

/-- HOL `zip_swap`（tame_list.hl:919
`MAP (\d. SND d, FST d) (zip x y) = zip y x`）。 -/
theorem zipSwapSpine (l₁ : List α) (l₂ : List β) :
    (l₁.zip l₂).map Prod.swap = l₂.zip l₁ :=
  List.zip_swap ..

/-- HOL `I_BIJ_EQ`（tame_list.hl:927 `BIJ I s t <=> s = t`）。 -/
theorem iBijEq {s t : Set α} : Set.BijOn id s t ↔ s = t := by
  constructor
  · intro h
    have hST : s ⊆ t := fun x hx => h.1 hx
    have hTS : t ⊆ s := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := h.2.2 hx
      have hy' : y = x := hyx
      rw [← hy']
      exact hy
    exact hST.antisymm hTS
  · rintro rfl
    exact ⟨fun _ hx => hx, fun _ hx _ hy hab => hab, fun y hy => ⟨y, hy, rfl⟩⟩

/-! ### §14 indexl 首现语义（tame_list.hl:939/:1425-1466）

`indexl` ↦ `List.idxOf`（首现语义；`:988 indexl_map` 与 `:1453 index_rot`
的 Nodup 特形已由 TameLp la7_idxOf_map / la7_idxOf_rotOne 在账）。 -/

/-- HOL `indexl_uniq`（tame_list.hl:939
`uniq y /\ i < sizel y /\ nth x0 y i = d ==> indexl d y = i`）。 -/
theorem idxOfUniq {l : List α} [BEq α] [LawfulBEq α] (hn : l.Nodup) {i : ℕ} {d e : α}
    (hi : i < l.length) (h : l.getD i d = e) : l.idxOf e = i := by
  rw [← h, List.getD_eq_getElem _ _ hi]
  exact List.Nodup.idxOf_getElem hn i hi

/-- HOL `index_uniq`（tame_list.hl:1425
`MEM x s /\ MEM y s /\ indexl x s = indexl y s ==> x = y`）。 -/
theorem idxUniq {s : List α} [BEq α] [LawfulBEq α] {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (h : s.idxOf x = s.idxOf y) : x = y := by
  have hx' : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hy' : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hv : s[s.idxOf x] = s[s.idxOf y] := by simp only [h]
  exact (List.getElem_idxOf hx').symm.trans (hv.trans (List.getElem_idxOf hy'))

/-- HOL `index0`（tame_list.hl:1433
`MEM x s /\ indexl x s = 0 ==> x = HD s`）。 -/
theorem idxZero {s : List α} [Inhabited α] [BEq α] [LawfulBEq α] {x : α}
    (hx : x ∈ s) (h0 : s.idxOf x = 0) : x = s.head! := by
  cases s with
  | nil => cases hx
  | cons a t =>
    show x = a
    by_cases hxa : x = a
    · exact hxa
    · exfalso
      rw [List.idxOf_cons_ne t (Ne.symm hxa), Nat.succ_eq_add_one] at h0
      omega

/-- HOL `index_rot`（tame_list.hl:1453
`MEM x s /\ ~(x = HD s) ==> SUC (indexl x (rot 1 s)) = indexl x s`）——
无 Nodup 前提的首现语义一般形（Nodup 特形见 TameLp la7_idxOf_rotOne）。 -/
theorem idxOfRotateOne {s : List α} [Inhabited α] [BEq α] [LawfulBEq α] {x : α}
    (hx : x ∈ s) (hne : x ≠ s.head!) : (s.rotate 1).idxOf x + 1 = s.idxOf x := by
  cases s with
  | nil => cases hx
  | cons a t =>
    have hne' : x ≠ a := by simpa using hne
    have hxt : x ∈ t := by
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact absurd rfl hne'
      · exact hxt
    rw [List.rotate_cons_succ, List.rotate_zero, List.idxOf_append_of_mem hxt,
      List.idxOf_cons_ne t (Ne.symm hne'), Nat.succ_eq_add_one]

/-! ### §15 elements_of_list / list_of_darts 家族（tame_list.hl:1066-1136/:1249） -/

/-- HOL `elements_of_list`（list_hypermap-compiled.hl:29 载体）的成员刻画：
`x ∈ elements_of_list L <=> ?f. MEM f L /\ MEM x f`（:1066 `elements_of_list_unions`
与 :1082 的共用展开）。 -/
theorem memElementsOfListIff {L : fgraph ℕ} {x : ℕ} :
    x ∈ elementsOfList L ↔ ∃ f ∈ L, x ∈ f := by
  simp only [elementsOfList, listOfElements, Set.mem_setOf_eq, List.mem_eraseDups,
    List.mem_flatten]

/-- HOL `elements_of_list_unions`（tame_list.hl:1066
`elements_of_list L = UNIONS (IMAGE (\f. set_of_list f) (set_of_list L))`）；
`set_of_list` ↦ `Set`（`List.toSet`），成员逐槽经 `memElementsOfListIff`。 -/
theorem elementsOfListUnions (L : fgraph ℕ) :
    elementsOfList L = ⋃ f ∈ ({f : List ℕ | f ∈ L} : Set (List ℕ)), {x : ℕ | x ∈ f} := by
  ext x
  rw [Set.mem_iUnion₂]
  constructor
  · intro hx
    obtain ⟨f, hf, hxf⟩ := memElementsOfListIff.mp hx
    exact ⟨f, hf, hxf⟩
  · rintro ⟨f, hf, hxf⟩
    exact memElementsOfListIff.mpr ⟨f, hf, hxf⟩

/-- HOL `mem_list_of_darts_imp_mem_list_of_elements_alt`（tame_list.hl:1082
`MEM (a,b) (list_of_darts L) ==> MEM a (list_of_elements L) /\
MEM b (list_of_elements L)`）。 -/
theorem memDartsImpMemElements (L : fgraph ℕ) {a b : ℕ}
    (h : (a, b) ∈ listOfDarts L) :
    a ∈ listOfElements L ∧ b ∈ listOfElements L := by
  unfold listOfDarts at h
  simp only [List.mem_flatten, List.mem_map] at h
  obtain ⟨b, hb, hdb⟩ := h
  obtain ⟨l, hl, hlb⟩ := hb
  subst hlb
  have hdart := List.of_mem_zip hdb
  have ha : a ∈ l := hdart.1
  have hb : b ∈ l := by
    rcases List.mem_append.mp hdart.2 with hc | hc
    · exact List.drop_subset 1 l hc
    · exact List.take_subset 1 l hc
  exact ⟨List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨l, hl, ha⟩),
    List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨l, hl, hb⟩)⟩

/-- HOL `inj_on_imp_inj_dart`（tame_list.hl:1100
`inj_on phi (elements_of_list L) ==> !x y. MEM x (list_of_darts L) ==>
MEM y (list_of_darts L) ==> phi (FST x) = phi (FST y) /\ phi (SND x) = phi (SND y)
==> x = y`）。 -/
theorem injOnLiftListOfDarts (L : fgraph ℕ) {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) {d e : ℕ × ℕ}
    (hd : d ∈ listOfDarts L) (he : e ∈ listOfDarts L)
    (h : (phi d.1, phi d.2) = (phi e.1, phi e.2)) : d = e := by
  have hflat := (injOn_elementsOfList_iff.mp hinj)
  have h1 : phi d.1 = phi e.1 := congrArg Prod.fst h
  have h2 : phi d.2 = phi e.2 := congrArg Prod.snd h
  have hd1 : d.1 ∈ L.flatten ∧ d.2 ∈ L.flatten := by
    unfold listOfDarts at hd
    simp only [List.mem_flatten, List.mem_map] at hd
    obtain ⟨p, hp, hdp⟩ := hd
    obtain ⟨q, hq, hqp⟩ := hp
    subst hqp
    have hzip := List.of_mem_zip hdp
    refine ⟨List.mem_flatten.mpr ⟨q, hq, hzip.1⟩, ?_⟩
    rcases List.mem_append.mp hzip.2 with hc | hc
    · exact List.mem_flatten.mpr ⟨q, hq, List.drop_subset 1 q hc⟩
    · exact List.mem_flatten.mpr ⟨q, hq, List.take_subset 1 q hc⟩
  have he1 : e.1 ∈ L.flatten ∧ e.2 ∈ L.flatten := by
    unfold listOfDarts at he
    simp only [List.mem_flatten, List.mem_map] at he
    obtain ⟨p, hp, hep⟩ := he
    obtain ⟨q, hq, hqp⟩ := hp
    subst hqp
    have hzip := List.of_mem_zip hep
    refine ⟨List.mem_flatten.mpr ⟨q, hq, hzip.1⟩, ?_⟩
    rcases List.mem_append.mp hzip.2 with hc | hc
    · exact List.mem_flatten.mpr ⟨q, hq, List.drop_subset 1 q hc⟩
    · exact List.mem_flatten.mpr ⟨q, hq, List.take_subset 1 q hc⟩
  show (d.1, d.2) = (e.1, e.2)
  rw [hflat d.1 hd1.1 e.1 he1.1 h1, hflat d.2 hd1.2 e.2 he1.2 h2]

/-- HOL `BIJ_IMAGE_darts_of_list`（tame_list.hl:1121
`good_list x /\ inj_on phi (elements_of x) ==>
BIJ (\u. phi (FST u), phi (SND u)) (darts_of_list x)
(darts_of_list (MAP (MAP phi) x))`）。诚实记账：`good_list x` 前提在 HOL
证明体（ONE_ONE_IMP_BIJ_IMAGE 只用单射性 + :1051 像方程）中未被消费，
按原文携带。`darts_of_list` ↦ `{d | d ∈ listOfDarts _}`（set_of_list 形）。 -/
theorem bijImageLiftListOfDarts {L : fgraph ℕ} {phi : ℕ → ℕ}
    (_hgood : GoodList L) (hinj : Set.InjOn phi (elementsOfList L)) :
    Set.BijOn (fun u : ℕ × ℕ => (phi u.1, phi u.2)) {d | d ∈ listOfDarts L}
      {d | d ∈ listOfDarts (L.map (List.map phi))} := by
  have hmap := TameLp.la7_listOfDarts_map L phi
  refine ⟨fun d hd => ?_, fun d hd e he hcon => injOnLiftListOfDarts L hinj hd he hcon,
    fun y hy => ?_⟩
  · simp only [Set.mem_setOf_eq] at hd ⊢
    rw [hmap]
    exact List.mem_map_of_mem hd
  · simp only [Set.mem_setOf_eq] at hy ⊢
    rw [hmap] at hy
    obtain ⟨d, hd, hdy⟩ := List.mem_map.mp hy
    exact ⟨d, hd, hdy⟩

/-! ### §16 filter / undup / replicate（tame_list.hl:1274-1335） -/

/-- HOL `FILTER_CONJ`（tame_list.hl:1274
`FILTER f (FILTER g xs) = FILTER (\x. f x /\ g x) xs`）。 -/
theorem filterConj {f g : α → Bool} (l : List α) :
    (l.filter g).filter f = l.filter (fun x => f x && g x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h1 : g a = true <;> by_cases h2 : f a = true <;>
      simp [List.filter_cons, h1, h2, ih]

/-- HOL `FILTER_NEGATE`（tame_list.hl:1287
`FILTER f xs = xs <=> FILTER (\x. ~(f x)) xs = []`）。 -/
theorem filterNegate {p : α → Bool} (l : List α) :
    l.filter p = l ↔ (l.filter (fun x => !p x)) = [] := by
  constructor
  · intro h
    rw [List.filter_eq_nil_iff]
    intro a ha
    have hpa := List.filter_eq_self.mp h a ha
    simp [hpa]
  · intro h
    rw [List.filter_eq_self]
    intro a ha
    by_contra hc
    have hnp : (!p a) = true := by simpa using hc
    have := List.filter_eq_nil_iff.mp h a ha
    simp [hnp] at this

/-- HOL `undup_cat`（tame_list.hl:1309
`(!x. MEM x s ==> MEM x t) ==> undup (cat s t) = undup t`）的成员形。
诚实收窄记账：HOL `undup`（Seq 库）为「保最后一次出现」递归
（`undup (x::l) = if x ∈ l then undup l else x :: undup l`），Lean
`List.eraseDups` 为「保首次出现」（removeAll 递归）——两语义对同一表的
去重结果列表可不同序（例：s = [x]、t = [a, x] 时 HOL 形成立而
eraseDups 形不成立），列表等式形不可直译；下游消费实为成员谓词，
按成员形收窄落地（两语义下成员谓词一致，`List.mem_eraseDups`）。 -/
theorem undupCat_mem {s t : List α} [BEq α] [LawfulBEq α] (h : ∀ x ∈ s, x ∈ t) :
    ∀ b, b ∈ (s ++ t).eraseDups ↔ b ∈ t.eraseDups := by
  intro b
  constructor
  · intro hmem
    rcases List.mem_append.mp (List.mem_eraseDups.mp hmem) with hbs | hbt
    · exact List.mem_eraseDups.mpr (h b hbs)
    · exact List.mem_eraseDups.mpr hbt
  · intro hbt
    have h1 := List.mem_eraseDups.mp hbt
    have h2 : b ∈ s ++ t := List.mem_append.mpr (Or.inr h1)
    exact List.mem_eraseDups.mpr h2

/-- HOL `EL_REPLICATE`（tame_list.hl:1324 `i < n ==> EL i (REPLICATE n s) = s`）。 -/
theorem elReplicate {n i : ℕ} {s d : α} (h : i < n) :
    (List.replicate n s).getD i d = s := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact h)]
  exact List.getElem_replicate (by rw [List.length_replicate]; exact h)

/-! ### §17 last / next_el / 杂件（tame_list.hl:1338-1417） -/

/-- HOL `next_el1`（tame_list.hl:1338 `next_el [h] h = h`）。 -/
theorem nextElOne {α : Type*} [BEq α] [LawfulBEq α] (h : α) : nextEl [h] h = h := by
  simp [nextEl]

/-- HOL `last_LAST`（tame_list.hl:1352 `~(s = []) ==> last x0 s = LAST s`）。 -/
theorem lastLastD {s : List α} {d : α} (hne : s ≠ []) : s.getLastD d = s.getLast hne := by
  cases s with
  | nil => exact absurd rfl hne
  | cons a t =>
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl

/-- HOL `MEM_LAST`（tame_list.hl:1364 `~(s = []) ==> MEM (LAST s) s`）。 -/
theorem memLastSpine {s : List α} (hne : s ≠ []) : s.getLast hne ∈ s :=
  List.getLast_mem hne

/-- HOL `uniq_last`（tame_list.hl:1378
`~(MEM h s) /\ ~(s = []) ==> ~(LAST (h::s) = h)`）。 -/
theorem uniqLastSpine {h : α} {s : List α} (hmem : h ∉ s) (hne : s ≠ []) :
    (h :: s).getLast (List.cons_ne_nil h s) ≠ h := by
  rw [List.getLast_cons hne]
  intro hc
  have hm := List.getLast_mem hne
  rw [hc] at hm
  exact hmem hm

/-- HOL `rcons_nonnil`（tame_list.hl:1417 `~(rcons s x = [])`；
`rcons` ↦ `l ++ [x]`）。 -/
theorem rconsNonnil (l : List α) (x : α) : l ++ [x] ≠ [] := by
  simp

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；预期标准三 `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.congsRot
#print axioms Kepler.Text.TameSpine.memListPairsIota
#print axioms Kepler.Text.TameSpine.bijImageLiftListOfDarts
#print axioms Kepler.Text.TameSpine.cardUpt
-/
