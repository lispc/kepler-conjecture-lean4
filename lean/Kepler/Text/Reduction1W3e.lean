/-
  Kepler.Text.Reduction1W3e — J4 Wave W3 第二波（余量）：图级 finals 簇图层七件
  （HOL reduction1.hl:2562-:2776：`subdivFace0_alt_mem` / `split_face_nonfinal2` /
  `subdivFace0_alt_finals` / `size_filter_replace_mono` / `makeFaceFinal_mono` /
  `subdivFace0_alt_final` / `generatePolygon_mono`）。簇内列表层三件
  （poioj 等）在 Reduction1W3f；两文件合计簇 10/10。

  白捡面裁定（工单第 3 条首步）：`Reduction3Thm7F.splitFaceFinals`（= HOL
  `splitFace_finals` :2588，公开件）**同证重落为本文件私件**——该文件源码已落库
  （9e54540f）但其 olean 不在编译池，岛编 import 不可用，且不替编排者装既有件池；
  其两个 private 前置（filter-replace 单点、`MEM_splitFace2`）一并同证重落
  （各 3-10 行）。`subdivFace0_alt` 三件（mem/final/finals）共用一个「沿
  splitFace 步保持不变量」私件——HOL 三件各自内联同一 LIST_INDUCT（none 跳步 /
  nextVertex 同步跳步 / splitFace 分裂），此处合一。

  `generatePolygon_mono` 的 Lean 路线短于 HOL：HOL 经 `subdivFaceFinal_eq`
  （需 `~(vos = [])`，故再引 enumerator_nil/indexToVertexList_nil）把
  `subdivFace` 换成 `subdivFaceFinal`；Lean 的 `subdivFace` 对任意 `vos` 定义性
  展开为 `subdivFace' … vos.head!.get! 0 vos.tail`，直接接已落件
  `subdivFace0Final`（Reduction1W2c），无需非空前提，也不依赖尚未入库的
  `subdivFaceFinal` 定义与 `subdivFaceFinal_eq`。HOL 前提 `planegraph g` 在其
  证体内零消费，按 W2j 先例省略（合法增强）。

  载体：`SND f` ↦ `f.final`、`FST/SND fg'` ↦ `.1`/`.2`、`finalGraph g` ↦
  `Graph.final g = true`；`subdivFace0Alt`/`splitFace`/`split_face`/
  `makeFaceFinal`/`finals`/`nonFinals`/`replace`/`generatePolygon` 均为在库 def。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3DefsSubdivAlt
import Kepler.Text.Reduction1W2c
import Kepler.Text.TameSpine.TameList52
import Kepler.Graphs.ListAuxLemmas
import Kepler.Graphs.Plane

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Graphs (Face Graph finals nonFinals makeFaceFinal setFinal replace replace3
  splitFace split_face subdivFace subdivFace' generatePolygon minimalFace enumerator
  indexToVertexList containsDuplicateEdge)
open Kepler.Text.Reduction3 (subdivFace0Alt subdivFace0AltNil)

/-! ## §0 私件：splitFace 两小事实 + filter-replace（Thm7F 同证重落） -/

/-- filter 对 `replace x [y]` 单点替换不变（被换元与新元均不满足 `P`；
Thm7F `t7f_filterReplaceSingleton` 同证重落）。 -/
private theorem filterReplaceSingleton {α : Type} {P : α → Bool} [BEq α] [LawfulBEq α]
    {x y : α} {xs : List α} (hx : P x = false) (hy : P y = false) :
    (replace x [y] xs).filter P = xs.filter P := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    by_cases hzx : z = x
    · subst hzx
      have e1 : replace z [y] (z :: zs) = [y] ++ zs := by
        simp only [replace, beq_self_eq_true, ↓reduceIte]
      have e2 : [y].filter P = [] := by
        rw [List.filter_cons, if_neg (by simp [hy]), List.filter_nil]
      have e3 : (z :: zs).filter P = zs.filter P := by
        rw [List.filter_cons, if_neg (by simp [hx])]
      rw [e1, List.filter_append, e2, List.nil_append, e3]
    · have e1 : replace x [y] (z :: zs) = z :: replace x [y] zs := by
        simp only [replace, if_neg (fun h => hzx (beq_iff_eq.mp h))]
      rw [e1, List.filter_cons, List.filter_cons]
      by_cases hpz : P z = true
      · rw [if_pos hpz, if_pos hpz, ih]
      · rw [if_neg hpz, if_neg hpz, ih]

/-- HOL `splitFace_finals`（reduction1.hl:2588-:2612；Thm7F 公开件
`splitFaceFinals` 同证重落）：
`f.final = false ⇒ finals (splitFace g u v f ws).2.2 = finals g`。 -/
private theorem splitFaceFinalsAux (g : Graph) (u v : Nat) (f : Face) (ws : List Nat)
    (hfin : f.final = false) :
    finals (splitFace g u v f ws).2.2 = finals g := by
  have hf1 : (split_face f u v ws).1.final = false := rfl
  have hf2 : (split_face f u v ws).2.final = false := rfl
  show (replace f [(split_face f u v ws).2] g.faces
        ++ [(split_face f u v ws).1]).filter Face.final
      = g.faces.filter Face.final
  rw [List.filter_append,
    show ([(split_face f u v ws).1].filter Face.final) = [] from by simp [hf1],
    List.append_nil]
  exact filterReplaceSingleton hfin hf2

/-- HOL `MEM_splitFace2`（tame_list.hl:4750；Thm7F 私件同证重落）：
`f ∈ g.faces ⇒ (splitFace g u v f ws).2.1 ∈ (splitFace g u v f ws).2.2.faces`。 -/
private theorem memSplitFace2 (g : Graph) (u v : Nat) (f : Face) (ws : List Nat)
    (hf : f ∈ g.faces) :
    (splitFace g u v f ws).2.1 ∈ (splitFace g u v f ws).2.2.faces := by
  show (split_face f u v ws).2 ∈
    replace f [(split_face f u v ws).2] g.faces ++ [(split_face f u v ws).1]
  exact List.mem_append_left _ (replace3 hf List.mem_cons_self)

/-! ## §1 `split_face_nonfinal2`（reduction1.hl:2614-:2625） -/

/-- **HOL `split_face_nonfinal2`**（reduction1.hl:2614-:2625）：
`let f1,f2 = split_face f u v ws in ~(SND f2)`——`split_face` 第二面非终面
（定义式 rfl；FaceDivisionProps1 `splitFace_nonFinal_face` 同体）。 -/
theorem splitFaceNonfinal2 (f : Face) (u v : Nat) (ws : List Nat) :
    (split_face f u v ws).2.final = false := rfl

/-! ## §2 subdivFace0_alt 不变量私件（三件共用同一归纳） -/

/-- `subdivFace0_alt` 沿 splitFace 步保持不变量 `Q`（HOL 三件
`subdivFace0_alt_mem` / `subdivFace0_alt_finals` / `subdivFace0_alt_final`
各自内联同一 LIST_INDUCT，此处合一；三支 = none 跳步 / nextVertex 同步跳步 /
splitFace 分裂）。 -/
private theorem subdivFace0AltInv {Q : Face → Graph → Prop}
    (hstep : ∀ g f u v ws, Q f g →
      Q (splitFace g u v f ws).2.1 (splitFace g u v f ws).2.2)
    (vs : List (Option Nat)) (g : Graph) (f : Face) (u n : Nat) (h : Q f g) :
    Q (subdivFace0Alt g f u n vs).1 (subdivFace0Alt g f u n vs).2 := by
  induction vs generalizing g f u n with
  | nil => rw [subdivFace0AltNil]; exact h
  | cons vo vos ih =>
    have heq : subdivFace0Alt g f u n (vo :: vos) =
        (if vo = none then subdivFace0Alt g f u (n + 1) vos
         else if (f.nextVertex u == vo.getD 0 && n == 0) = true then
           subdivFace0Alt g f (vo.getD 0) 0 vos
         else
           subdivFace0Alt
             (splitFace g u (vo.getD 0) f (List.range' g.countVertices n)).2.2
             (splitFace g u (vo.getD 0) f (List.range' g.countVertices n)).2.1
             (vo.getD 0) 0 vos) := rfl
    rw [heq]
    by_cases h1 : vo = none
    · rw [if_pos h1]
      exact ih g f u (n + 1) h
    · rw [if_neg h1]
      by_cases h2 : (f.nextVertex u == vo.getD 0 && n == 0) = true
      · rw [if_pos h2]
        exact ih g f (vo.getD 0) 0 h
      · rw [if_neg h2]
        exact ih
          (splitFace g u (vo.getD 0) f (List.range' g.countVertices n)).2.2
          (splitFace g u (vo.getD 0) f (List.range' g.countVertices n)).2.1
          (vo.getD 0) 0 (hstep g f u (vo.getD 0) _ h)

/-! ## §3 subdivFace0_alt 三件（reduction1.hl:2562-:2586、:2627-:2665、:2701-:2723） -/

/-- **HOL `subdivFace0_alt_mem`**（reduction1.hl:2562-:2586）：
`MEM f (faces g) ⇒ MEM (FST (subdivFace0_alt g f r n vs))
(faces (SND (subdivFace0_alt g f r n vs)))`。 -/
theorem subdivFace0AltMem (vs : List (Option Nat)) (g : Graph) (f : Face) (r n : Nat)
    (hf : f ∈ g.faces) :
    (subdivFace0Alt g f r n vs).1 ∈ (subdivFace0Alt g f r n vs).2.faces := by
  refine subdivFace0AltInv (Q := fun ff gg => ff ∈ gg.faces) ?_ vs g f r n hf
  intro g0 f0 u v ws h0
  exact memSplitFace2 g0 u v f0 ws h0

/-- **HOL `subdivFace0_alt_final`**（reduction1.hl:2701-:2723）：
`~SND f ==> ~SND (FST (subdivFace0_alt g f h n vs))`。 -/
theorem subdivFace0AltFinal (vs : List (Option Nat)) (g : Graph) (f : Face)
    (h n : Nat) (hfin : f.final = false) :
    (subdivFace0Alt g f h n vs).1.final = false := by
  refine subdivFace0AltInv (Q := fun ff _ => ff.final = false) ?_ vs g f h n hfin
  intro g0 f0 u v ws _
  exact splitFaceNonfinal2 f0 u v ws

/-- **HOL `subdivFace0_alt_finals`**（reduction1.hl:2627-:2665）：
`MEM f (faces g) /\ ~SND f ==>
finals g = finals (SND (subdivFace0_alt g f u n vs))`。 -/
theorem subdivFace0AltFinals (vs : List (Option Nat)) (g : Graph) (f : Face)
    (u n : Nat) (hf : f ∈ g.faces) (hfin : f.final = false) :
    finals g = finals (subdivFace0Alt g f u n vs).2 := by
  have hInv := subdivFace0AltInv
    (Q := fun ff gg => ff ∈ gg.faces ∧ ff.final = false ∧ finals gg = finals g)
    (fun g0 f0 u0 v0 ws h0 => ⟨memSplitFace2 g0 u0 v0 f0 ws h0.1,
      splitFaceNonfinal2 f0 u0 v0 ws,
      (splitFaceFinalsAux g0 u0 v0 f0 ws h0.2.1).trans h0.2.2⟩)
    vs g f u n ⟨hf, hfin, rfl⟩
  exact hInv.2.2.symm

/-! ## §4 filter-replace 单调两件（reduction1.hl:2667-:2699） -/

/-- **HOL `size_filter_replace_mono`**（reduction1.hl:2667-:2686）：
`MEM x xs ∧ ¬P x ∧ P x' ⇒
sizel (filter P xs) < sizel (filter P (replace x [x'] xs))`。 -/
theorem sizeFilterReplaceMono {α : Type} {P : α → Bool} [BEq α] [LawfulBEq α]
    {xs : List α} {x x' : α} (hx : x ∈ xs) (hPx : P x = false) (hPx' : P x' = true) :
    (xs.filter P).length < ((replace x [x'] xs).filter P).length := by
  induction xs with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons z zs ih =>
    by_cases hzx : z = x
    · subst hzx
      have e1 : replace z [x'] (z :: zs) = [x'] ++ zs := by
        simp only [replace, beq_self_eq_true, ↓reduceIte]
      have eL : (z :: zs).filter P = zs.filter P := by
        rw [List.filter_cons, if_neg (by simp [hPx])]
      have eR : ([x'] ++ zs).filter P = x' :: zs.filter P := by
        rw [List.filter_append, List.filter_cons, if_pos hPx', List.filter_nil,
          List.singleton_append]
      rw [e1, eL, eR, List.length_cons]
      exact Nat.lt_succ_self _
    · rw [show replace x [x'] (z :: zs) = z :: replace x [x'] zs from by
        simp only [replace, if_neg (fun h => hzx (beq_iff_eq.mp h))]]
      rw [List.filter_cons, List.filter_cons]
      have hxz : x ∈ zs := by
        rcases List.mem_cons.mp hx with hx1 | hx1
        · exact absurd hx1.symm hzx
        · exact hx1
      by_cases hpz : P z = true
      · rw [if_pos hpz, if_pos hpz]
        exact Nat.succ_lt_succ (ih hxz)
      · rw [if_neg hpz, if_neg hpz]
        exact ih hxz

/-- **HOL `makeFaceFinal_mono`**（reduction1.hl:2688-:2699）：
`MEM f (faces g) ∧ ¬SND f ⇒
sizel (finals g) < sizel (finals (makeFaceFinal f g))`。 -/
theorem makeFaceFinalMono (g : Graph) (f : Face) (hf : f ∈ g.faces)
    (hfin : f.final = false) :
    (finals g).length < (finals (makeFaceFinal f g)).length := by
  show (g.faces.filter Face.final).length <
      ((replace f [setFinal f] g.faces).filter Face.final).length
  exact sizeFilterReplaceMono hf hfin rfl

/-! ## §5 `generatePolygon_mono`（reduction1.hl:2725-:2776） -/

/-- **HOL `generatePolygon_mono`**（reduction1.hl:2725-:2776）：
`planegraph g /\ ~finalGraph g /\ nonFinals g = fs /\ minimalFace fs = f /\
MEM g' (generatePolygon i v f g) ==> sizel (finals g) < sizel (finals g')`。
HOL 前提 `planegraph g` 在其证体内零消费，此处省略（合法增强，W2j 先例）。
证体：`g' = subdivFace g f vos`（generatePolygon 定义）=
`makeFaceFinal (alt).1 (alt).2`（`subdivFace0Final`，alt = subdivFace0_alt …），
`finals g = finals (alt).2`（§3 finals）后 `makeFaceFinal_mono` 收口
（§3 mem/final 供两前提）；`f` 的面成员与非终面性取自
`mem_minimalFace_nonFinals`（TameList52）。 -/
theorem generatePolygonMono {i v : Nat} {g : Graph} {f : Face} {fs : List Face}
    {g' : Graph}
    (hnf : Kepler.Graphs.Graph.final g = false)
    (hfs : nonFinals g = fs) (hf : minimalFace fs = f)
    (hg' : g' ∈ generatePolygon i v f g) :
    (finals g).length < (finals g').length := by
  subst hfs
  subst hf
  -- f = minimalFace (nonFinals g) ∈ g.faces 且非终面
  have hne : nonFinals g ≠ [] := by
    intro hc
    have h1 : Kepler.Graphs.Graph.final g = true := by
      show (nonFinals g).isEmpty = true
      rw [hc]
      rfl
    rw [h1] at hnf
    exact Bool.noConfusion hnf
  have hmem : minimalFace (nonFinals g) ∈ g.faces.filter (fun f => !f.final) :=
    Kepler.Text.TameSpine.memMinimalFaceNonFinals g hne
  obtain ⟨hfF, hfnf⟩ := List.mem_filter.mp hmem
  have hfin : (minimalFace (nonFinals g)).final = false := by simpa using hfnf
  -- g' = subdivFace g f vos
  have hg2 : g' ∈ (((enumerator i (minimalFace (nonFinals g)).vertices.length).filter
      (fun is => !containsDuplicateEdge g (minimalFace (nonFinals g)) v is)).map
      (indexToVertexList (minimalFace (nonFinals g)) v)).map
      (subdivFace g (minimalFace (nonFinals g))) := hg'
  obtain ⟨vos, -, hsub⟩ := List.mem_map.mp hg2
  rw [← hsub]
  show (finals g).length < (finals (subdivFace' g (minimalFace (nonFinals g))
    vos.head!.get! 0 vos.tail)).length
  rw [← subdivFace0Final g (minimalFace (nonFinals g)) vos.head!.get! 0 vos.tail]
  show (finals g).length <
    (finals (makeFaceFinal
      (subdivFace0Alt g (minimalFace (nonFinals g)) vos.head!.get! 0 vos.tail).1
      (subdivFace0Alt g (minimalFace (nonFinals g)) vos.head!.get! 0 vos.tail).2)).length
  rw [subdivFace0AltFinals vos.tail g (minimalFace (nonFinals g)) vos.head!.get! 0 hfF hfin]
  exact makeFaceFinalMono _ _
    (subdivFace0AltMem vos.tail g (minimalFace (nonFinals g)) vos.head!.get! 0 hfF)
    (subdivFace0AltFinal vos.tail g (minimalFace (nonFinals g)) vos.head!.get! 0 hfin)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.splitFaceNonfinal2
#print axioms Kepler.Text.Reduction1.subdivFace0AltMem
#print axioms Kepler.Text.Reduction1.subdivFace0AltFinal
#print axioms Kepler.Text.Reduction1.subdivFace0AltFinals
#print axioms Kepler.Text.Reduction1.sizeFilterReplaceMono
#print axioms Kepler.Text.Reduction1.makeFaceFinalMono
#print axioms Kepler.Text.Reduction1.generatePolygonMono
