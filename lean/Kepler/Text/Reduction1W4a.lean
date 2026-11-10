/-
  Kepler.Text.Reduction1W4a — J4 Wave W4-1 桥基段 + W4-2 makeFaceFinal 簇三件
  （HOL reduction1.hl:4040-:4112 / :4243-:4274 / :4275-:4291 / :4369-:4392）：
  `RTranCl_trans` / `planegraphP_trans` / `sizel_faceListAt_seed` /
  `sizel_faceListAt` / `is_restricted_size_face2` / `perm_eq_replace_hd` /
  `perm_eq_replace` / `makeFaceFinal_planegraphP` / `facesAt_filter_makeFaceFinal` /
  `mem_faces_makeFaceFinal`。`mem_makeFaceFinal_planeGraphP_etc`（:4393，156 行
  最大件）留 W4-2 收尾波。

  **查重记账（按 HOL 原名搜 docstring + 语义双路）**：
  · `sizel_faceListAt_seed`（:4114）语义已在库：`Kepler.Graphs.
    Seed_holds_faceListAt_len`（InvariantsC:1385，Isabelle 移植层命名，
    docstring 引 Invariants.thy 而非 HOL 名，故按 HOL 名搜不到）。本文件
    **不重证**，只立一行别名件作 HOL 名锚（TameList5 `XKDZKWV` 别名先例）。
  · `RTranCl_trans`（:4040）语义有 private 同证件 `Worklist.
    RTranCl_succs_right`（不可跨文件消费）——本文件同证重落为公开件。
  · 其余八件全树零命中（HOL 名与驼峰名双搜），新落。
  · 原 W4-1 工单表中的 `minimalVertex_in_minimalFace`（:4549）经注释嵌套
    深度核查为 **HOL 死码**（整块在 `(* … *)` 内，:4562 尾随 `*)`），不搬。
    同法重核 W4 全区：`not_containsDuplicateEdge_iota`（:3764）与
    `iota_generatePolygon`（:3776）亦为死码（上轮 W4 表按 `^let` 直搜未扣
    注释，此处勘误：两件属「HOL 死码禁搬」，非「已在库」）。

  **陈述偏离清单（逐条，均非省前提）**：
  ① `RTranCl_trans`：HOL 泛型 `(g0:A)`；Lean 载体 `Kepler.Graphs.RTranCl`
     本身即特化于 `Graph`（Plane.lean:17，`RTranCl_induct` 同特化）——按
     载体落 Graph 形，非收窄选择。
  ② `perm_eq_replace_hd` 的 `HD s' = x` ↦ `s'.head! = x`（`[Inhabited α]`，
     TameSpine 批 3 `head!` 约定；证人 `x :: s.erase x` 非空，junk 支不触及）。
  ③ `perm_eq` ↦ `List.Perm`（树内既定载体：`GoodFacesV3` 即
     `(facesAtV2 g v).Perm (g.facesAt v)`）；`replace` ↦ `Kepler.Graphs.replace`
     （第二参为列表，与 HOL `replace_hd : replace (HD b) f b = cat f (TL b)`
     同型）。实例取 `[BEq α] [LawfulBEq α]` 显式绑定——下游在 `Face` 上消费
     （`makeFaceFinalFaceList`），`Face` 同时有派生 BEq 与 DecidableEq 诱导
     BEq 两实例，显式绑定可任取其一。
  ④ W4-2 三件的 `GoodFacesV3`/`VerticesSet2Eq` 取 TameCorrList 载体（同
     `allSomeGeneratePolygon` 既落形）；`finalGraph g` ↦ `Graph.final g = true`。
  **本文件零省前提**：十件的 HOL 前提全部保留、原序。

  证体与 HOL 的差异（路线更短处）：
  · `sizel_faceListAt`：HOL 50 行沿 `planegraph_induct` + `subdivFace0_induct`
    手工归纳；Lean 侧图层已有不变量机器（`inv` ∋ `faceListAt_len`、
    `inv_Seed`、`inv_inv_next_plane`、`RTranCl_induct`），四行收口。
  · `perm_eq_replace(_hd)`：HOL 经 `cat_to_fst` 把 `x` 挪到表头再
    `replace_hd`/`replace_cat2`；Lean 走私件
    `replace x ys s ~ ys ++ s.erase x`（`x ∈ s`），两件各数行。
  · `facesAt_filter_makeFaceFinal`：HOL 该步隐于 REWRITE 链的
    「`replace f [setFinal f]` 与 `filter` 交换」落为私件 `filterReplaceComm`
    （条件 `P y = P x`，由 `setFinal` 保顶点表即得）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Graphs.PlaneProps
import Kepler.Graphs.Plane1Props
import Kepler.Graphs.InvariantsC
import Kepler.Graphs.ListAuxLemmas
import Kepler.Text.TameLp
import Kepler.Text.Reduction1W2x
import Kepler.Text.TameSpine.TameList56
import Kepler.Text.TameSpine.TameList58
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.TameCorrList

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Graphs (Graph fgraph RTranCl next_plane Seed replace Face makeFaceFinal
  makeFaceFinalFaceList setFinal finals generatePolygon maxGon minimalFace
  minimalVertex nonFinals)
open Kepler.Text.TameLp (hypermapOfList)
open Kepler.Text.TameSpine (PlaneGraphPSpine PlaneGraphSpine listOfFaces)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq facesAtV2)
open Kepler.Assembly (GoodList listPairs)

/-! ## §0 私件：getD 沿 map 提取 -/

/-- `v < l.length` 时 `l.map F` 的 `getD` 可提出 `F`。 -/
private theorem getDMapOfMem {α : Type} {β : Type} {F : α → β} {d : β} {d' : α}
    {l : List α} {v : ℕ} (hv : v < l.length) :
    (l.map F).getD v d = F (l.getD v d') := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hv]
  simp

/-! ## §1 RTranCl / planegraphP 尾步（reduction1.hl:4040-:4070） -/

/-- **HOL `RTranCl_trans`**（reduction1.hl:4040-:4055）：
`g0,g1 IN RTranCl suc /\ MEM g2 (suc g1) ==> g0,g2 IN RTranCl suc`——
RTranCl 的尾步延拓（Lean 构造子 `succs` 是头步，尾步需对路径归纳；
`Worklist.RTranCl_succs_right` private 同证）。载体：`Kepler.Graphs.RTranCl`
特化于 `Graph`（文件头偏离①）。 -/
theorem rTranClTrans {suc : Graph → List Graph} {g0 g1 g2 : Graph}
    (h01 : RTranCl suc g0 g1) (h12 : g2 ∈ suc g1) : RTranCl suc g0 g2 := by
  induction h01 with
  | refl => exact RTranCl.succs h12 RTranCl.refl
  | succs hy _ ih => exact RTranCl.succs hy (ih h12)

/-- **HOL `planegraphP_trans`**（reduction1.hl:4057-:4069）：
`planegraphP p g /\ MEM g' (next_plane p g) ==> planegraphP p g'`。 -/
theorem planegraphPTrans {g g' : Graph} {p : ℕ}
    (h : PlaneGraphPSpine p g) (hg' : g' ∈ next_plane p g) :
    PlaneGraphPSpine p g' :=
  rTranClTrans h hg'

/-! ## §2 faceListAt 长度（reduction1.hl:4114-:4172） -/

/-- **HOL `sizel_faceListAt_seed`**（reduction1.hl:4114-:4121）：
`sizel (faceListAt (Seed p)) = countVertices (Seed p)`——**HOL 名锚别名件**：
语义已在库（`Kepler.Graphs.Seed_holds_faceListAt_len`，InvariantsC:1385），
此处不重证，仅供按 HOL 名检索（TameList5 `XKDZKWV` 别名先例）。 -/
theorem sizelFaceListAtSeed (p : ℕ) :
    (Seed p).faceListAt.length = (Seed p).countVertices :=
  Kepler.Graphs.Seed_holds_faceListAt_len

/-- **HOL `sizel_faceListAt`**（reduction1.hl:4123-:4171）：
`planegraph g ==> sizel (faceListAt g) = countVertices g`——图层不变量
`inv`（含 `faceListAt_len`）沿 `next_plane` 的保持（`inv_Seed` +
`inv_inv_next_plane`）经 `RTranCl_induct` 直取。`planegraph g` ↦
`PlaneGraphSpine g`（TameList58，`∃ p, PlaneGraphPSpine p g`）。 -/
theorem sizelFaceListAt {g : Graph} (hp : PlaneGraphSpine g) :
    g.faceListAt.length = g.countVertices := by
  obtain ⟨p, hp⟩ := hp
  have hinv : Kepler.Graphs.inv g :=
    Kepler.Graphs.RTranCl_induct hp Kepler.Graphs.inv_Seed
      Kepler.Graphs.inv_inv_next_plane
  exact hinv.1.2.2.1

/-! ## §3 `replace` 的 Perm 两件（reduction1.hl:4173-:4242） -/

/-- 私件：`x ∈ s` 时 `replace x ys s`（首现处换成 `ys`）与
`ys ++ s.erase x` 互为置换。 -/
private theorem replacePermErase {α : Type} [BEq α] [LawfulBEq α] {x : α}
    (ys : List α) {s : List α} (h : x ∈ s) :
    (replace x ys s).Perm (ys ++ s.erase x) := by
  induction s with
  | nil => exact absurd h (List.not_mem_nil)
  | cons z zs ih =>
    by_cases hzx : z = x
    · subst hzx
      have e1 : replace z ys (z :: zs) = ys ++ zs := by
        simp only [replace, beq_self_eq_true, ↓reduceIte]
      rw [e1, List.erase_cons_head]
    · have hxz : x ∈ zs := by
        rcases List.mem_cons.mp h with h1 | h1
        · exact absurd h1.symm hzx
        · exact h1
      have e1 : replace x ys (z :: zs) = z :: replace x ys zs := by
        simp only [replace, if_neg (fun hb => hzx (beq_iff_eq.mp hb))]
      have e2 : (z :: zs).erase x = z :: zs.erase x :=
        List.erase_cons_tail (fun hb => hzx (beq_iff_eq.mp hb))
      rw [e1, e2]
      exact ((ih hxz).cons z).trans List.perm_middle.symm

/-- **HOL `perm_eq_replace_hd`**（reduction1.hl:4173-:4203）：
`MEM x s ==> (?s'. perm_eq s s' /\ HD s' = x /\
perm_eq (replace x f s) (replace x f s'))`——证人 `x :: s.erase x`
（`HD` ↦ `head!`，文件头偏离②）。 -/
theorem permEqReplaceHd {α : Type} [BEq α] [LawfulBEq α] [Inhabited α]
    (x : α) (f : List α) {s : List α} (hx : x ∈ s) :
    ∃ s' : List α, s.Perm s' ∧ s'.head! = x ∧
      (replace x f s).Perm (replace x f s') := by
  refine ⟨x :: s.erase x, List.perm_cons_erase hx, rfl, ?_⟩
  have e1 : replace x f (x :: s.erase x) = f ++ s.erase x := by
    simp only [replace, beq_self_eq_true, ↓reduceIte]
  rw [e1]
  exact replacePermErase f hx

/-- **HOL `perm_eq_replace`**（reduction1.hl:4204-:4242）：
`perm_eq f g ==> perm_eq (replace a b f) (replace a b g)`——`a ∈ f` 时两侧
都与 `b ++ _.erase a` 置换（私件 + `Perm.erase`）；`a ∉ f` 时两侧 `replace`
恒等（`replace2`）。 -/
theorem permEqReplace {α : Type} [BEq α] [LawfulBEq α] {f g : List α}
    (a : α) (b : List α) (h : f.Perm g) :
    (replace a b f).Perm (replace a b g) := by
  by_cases ha : a ∈ f
  · have hag : a ∈ g := h.mem_iff.mp ha
    exact (replacePermErase b ha).trans
      (((h.erase a).append_left b).trans (replacePermErase b hag).symm)
  · have hag : a ∉ g := fun hc => ha (h.mem_iff.mpr hc)
    rw [Kepler.Graphs.replace2 ha, Kepler.Graphs.replace2 hag]
    exact h

/-! ## §4 `is_restricted_size_face2`（reduction1.hl:4275-:4291） -/

/-- **HOL `is_restricted_size_face2`**（reduction1.hl:4275-:4291）：
`good_list L /\ is_restricted (hypermap_of_list L) /\ MEM f (list_of_faces L)
==> 3 <= sizel f /\ sizel f <= foldr maxn 0 (MAP sizel L)`——首合取 =
`isRestrictedSizeFace`（TameList56）；次合取：`f = list_pairs l`、`l ∈ L`
（`list_of_faces` 定义）+ `size_list_pairs`（`la7_length_listPairs`）+
`foldr_size_max`（TameList59 `foldrSizeMax`）。`foldr maxn 0 (MAP sizel L)`
↦ `(L.map List.length).foldr max 0`（与 `maxFinalsGExists` 同载体）。 -/
theorem isRestrictedSizeFace2 (L : fgraph ℕ) (hL : GoodList L)
    (hres : (hypermapOfList L hL).IsRestricted) {f : List (ℕ × ℕ)}
    (hf : f ∈ listOfFaces L) :
    3 ≤ f.length ∧ f.length ≤ (L.map List.length).foldr max 0 := by
  refine ⟨Kepler.Text.TameSpine.isRestrictedSizeFace L hL hres hf, ?_⟩
  have hf' : f ∈ L.map listPairs := hf
  obtain ⟨l, hl, hlf⟩ := List.mem_map.mp hf'
  rw [← hlf, Kepler.Text.TameLp.la7_length_listPairs]
  exact Kepler.Text.TameSpine.foldrSizeMax hl

/-! ## §5 `makeFaceFinal_planegraphP`（reduction1.hl:4071-:4112） -/

/-- **HOL `makeFaceFinal_planegraphP`**（reduction1.hl:4071-:4112）：
`planegraphP p g /\ ~(finalGraph g) /\ minimalFace (nonFinals g) = f /\
minimalVertex g f = v /\ 3 ≤ sizel (FST f) /\ sizel (FST f) ≤ p + 3 /\
MEM v (FST f) /\ MEM (FST f) (fgraph g) /\ all uniq (fgraph g) /\
good_faces_v3 g /\ vertices_set2 g = elements_of_list (fgraph g) ==>
planegraphP p (makeFaceFinal f g)`——十一前提 HOL 原序（`GoodFacesV3`/
`VerticesSet2Eq` 载体同 `allSomeGeneratePolygon` 既落形）。证体：
`planegraphPTrans` + `next_plane` 展开（`fs.isEmpty` 假支）+
`generatePolygon (sizel (FST f)) v f g` 成员（`mem_makeFaceFinal_generatePolygon`，
Reduction1W2x）。 -/
theorem makeFaceFinalPlanegraphP {f : Face} {g : Graph} {p v : ℕ}
    (hpg : PlaneGraphPSpine p g)
    (hnf : Kepler.Graphs.Graph.final g = false)
    (hf : minimalFace (nonFinals g) = f)
    (hv : minimalVertex g f = v)
    (h3 : 3 ≤ f.vertices.length)
    (hle : f.vertices.length ≤ p + 3)
    (hvm : v ∈ f.vertices)
    (hfm : f.vertices ∈ g.fgraph)
    (hun : ∀ l ∈ g.fgraph, l.Nodup)
    (hgf : GoodFacesV3 g) (hvs2 : VerticesSet2Eq g) :
    PlaneGraphPSpine p (makeFaceFinal f g) := by
  refine planegraphPTrans hpg ?_
  have hne : (nonFinals g).isEmpty = false := hnf
  rw [show next_plane p g =
      (if (nonFinals g).isEmpty = true then []
       else (List.range' 3 (maxGon p - 2)).flatMap fun i =>
         generatePolygon i (minimalVertex g (minimalFace (nonFinals g)))
           (minimalFace (nonFinals g)) g) from rfl,
    if_neg (by rw [hne]; simp), hf, hv]
  refine List.mem_flatMap.mpr ⟨f.vertices.length, ?_, ?_⟩
  · rw [List.mem_range'_1]
    refine ⟨h3, ?_⟩
    rw [Kepler.Graphs.maxGon]
    omega
  · exact memMakeFaceFinalGeneratePolygon h3 hvm hfm hun hgf hvs2

/-! ## §6 `facesAt_filter_makeFaceFinal`（reduction1.hl:4243-:4274） -/

/-- 私件：`P y = P x` 时 `replace x [y]` 与 `filter P` 交换（HOL
`facesAt_filter_makeFaceFinal` 该步隐于 REWRITE 链）。 -/
private theorem filterReplaceComm {α : Type} [BEq α] [LawfulBEq α] {x y : α}
    {xs : List α} (P : α → Bool) (hPyx : P y = P x) :
    (replace x [y] xs).filter P = replace x [y] (xs.filter P) := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    by_cases hzx : z = x
    · subst hzx
      rw [show replace z [y] (z :: zs) = [y] ++ zs from by
        simp only [replace, beq_self_eq_true, ↓reduceIte]]
      by_cases hpz : P z = true
      · have hpy : P y = true := hPyx.trans hpz
        simp [hpz, hpy, replace]
      · have hpz' : P z = false := by simpa using hpz
        have hpy : P y = false := hPyx.trans hpz'
        simp [hpz', hpy]
        exact (Kepler.Graphs.replace2
          (fun hc => hpz (List.mem_filter.mp hc).2)).symm
    · rw [show replace x [y] (z :: zs) = z :: replace x [y] zs from by
        simp only [replace, if_neg (fun hb => hzx (beq_iff_eq.mp hb))]]
      rw [List.filter_cons, List.filter_cons]
      by_cases hpz : P z = true
      · rw [if_pos hpz, if_pos hpz, ih]
        exact (show replace x [y] (z :: zs.filter P) =
            z :: replace x [y] (zs.filter P) from by
          simp only [replace, if_neg (fun hb => hzx (beq_iff_eq.mp hb))]).symm
      · rw [if_neg hpz, if_neg hpz, ih]

/-- **HOL `facesAt_filter_makeFaceFinal`**（reduction1.hl:4243-:4274）：
`makeFaceFinal f g = g' /\ planegraph g /\ good_faces_v3 g ==>
good_faces_v3 g'`。证体：`vertices_set2` 只依赖 `countVertices`
（`makeFaceFinal` 保该字段），故 `GoodFacesV3` 假设对 `g'` 的顶点逐点可用；
`facesAt g' v = replace f [setFinal f] (facesAt g v)`（`getD` 沿 map 提取）、
`facesAt_v2 g' v = replace f [setFinal f] (facesAt_v2 g v)`（私件
`filterReplaceComm`），由假设的 Perm 经 `permEqReplace`（本文件 §3）换装。 -/
theorem facesAtFilterMakeFaceFinal {g g' : Graph} {f : Face}
    (hg' : makeFaceFinal f g = g')
    (hp : PlaneGraphSpine g) (hgf : GoodFacesV3 g) :
    GoodFacesV3 g' := by
  subst hg'
  intro v hv
  have hv2 : v ∈ Kepler.Text.TameCorrList.verticesSet2 g := hv
  have hperm := hgf v hv2
  have hvr : v ∈ List.range g.countVertices := hv2
  have hvlt : v < g.faceListAt.length := by
    rw [sizelFaceListAt hp]
    exact List.mem_range.mp hvr
  have hgetD : (makeFaceFinal f g).facesAt v =
      replace f [setFinal f] (g.facesAt v) := by
    show (g.faceListAt.map (makeFaceFinalFaceList f)).getD v [] =
      makeFaceFinalFaceList f (g.faceListAt.getD v [])
    exact getDMapOfMem hvlt
  have hfacesV2 : facesAtV2 (makeFaceFinal f g) v =
      replace f [setFinal f] (facesAtV2 g v) := by
    show ((replace f [setFinal f] g.faces).filter
      (fun f' => v ∈ f'.vertices)) = _
    exact filterReplaceComm _ rfl
  rw [hgetD, hfacesV2]
  exact permEqReplace f [setFinal f] hperm

/-! ## §7 `mem_faces_makeFaceFinal`（reduction1.hl:4369-:4392） -/

/-- **HOL `mem_faces_makeFaceFinal`**（reduction1.hl:4369-:4392）：
`MEM f' (filter SND (faces (makeFaceFinal f g))) ⇒
f' = setFinal f ∨ MEM f' (filter SND (faces g))`——`replace5` 两支
（无 Nodup 前提；HOL 逐表归纳与 `replace5` 同证）。载体：`filter SND
(faces g)` ↦ `finals g`。 -/
theorem memFacesMakeFaceFinal (g : Graph) (f f' : Face)
    (h : f' ∈ finals (makeFaceFinal f g)) :
    f' = setFinal f ∨ f' ∈ finals g := by
  have h' : f' ∈ (replace f [setFinal f] g.faces).filter Face.final := h
  obtain ⟨hmem, hfin⟩ := List.mem_filter.mp h'
  rcases Kepler.Graphs.replace5 hmem with h1 | h1
  · exact Or.inr (List.mem_filter.mpr ⟨h1, hfin⟩)
  · exact Or.inl (List.mem_singleton.mp h1)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.rTranClTrans
#print axioms Kepler.Text.Reduction1.planegraphPTrans
#print axioms Kepler.Text.Reduction1.sizelFaceListAtSeed
#print axioms Kepler.Text.Reduction1.sizelFaceListAt
#print axioms Kepler.Text.Reduction1.permEqReplaceHd
#print axioms Kepler.Text.Reduction1.permEqReplace
#print axioms Kepler.Text.Reduction1.isRestrictedSizeFace2
#print axioms Kepler.Text.Reduction1.makeFaceFinalPlanegraphP
#print axioms Kepler.Text.Reduction1.facesAtFilterMakeFaceFinal
#print axioms Kepler.Text.Reduction1.memFacesMakeFaceFinal
