/-
  Kepler.Text.Reduction1W2x — J4 W2 遗留链补齐（编排者续843 续派）：四件
  （HOL reduction1.hl:1586-:1781：`rotate_subdivFace0_alt` /
  `rotate_subdivFaceFinal` / `subdivFaceFinal_eq` /
  `mem_makeFaceFinal_generatePolygon`）。

  **`subdivFaceFinal` 定义可省的机器证明（工单红线项）**：全源 grep
  （text_formalization/*.hl，排除 `subdivFaceFinal2`）显示该常量只出现在
  **两条自身引理的陈述**（:1689 / :1719）；其余出现全为证体中转——引
  `rotate_subdivFaceFinal`/`subdivFaceFinal_eq` 后立刻 `REWRITE_TAC
  [subdivFaceFinal]` 展开定义（reduction1 :1692/:1722/:1745/:1748/:2739/:2745、
  reduction3:1485-1486）；`more_tame_concl.hl:450` 只是项绑定非定理；无任何
  终端消费者陈述含它（`mem_makeFaceFinal_generatePolygon` 与
  `generatePolygon_mono` 的陈述均 def-free）。本文件四件以
  **`makeFaceFinal ∘ subdivFace0Alt` 展开形**落库（docstring 标注 HOL
  `subdivFaceFinal` 的展开形），`memMakeFaceFinalGeneratePolygon` 走
  `rotateSubdivFace0Alt` + `subdivFace0Final`（W2c）+ `allSomeGeneratePolygon`
  （W2d）绕行、绿——即定义与 `subdivFaceFinal_eq`-常量形在 Lean 侧可省、
  DEF-FIX 不必启的机器证据。

  载体：`sizel (FST f)` ↦ `f.vertices.length`、`FST f` ↦ `f.vertices`、
  `fgraph g` ↦ `g.fgraph`（= `g.faces.map Face.vertices`）、`the (HD vs)` ↦
  `vs.head!.get!`（与在库 `subdivFace` 定义同形）、`dropl n l` ↦ `l.drop n`、
  `MAP SOME l` ↦ `l.map Option.some`；`rotate_to` 取
  `Kepler.Text.Reduction3.rotateTo`（与 `allSomeGeneratePolygon` 陈述同库，
  内部经 W2d `rotateToBridge`（rfl）换 TameSpine 系引理）。
  `subdivFaceFinal_eq` 的 HOL 前提 `~(vos = [])` 在 Lean 载体下不需要
  （`subdivFace` 的 `head!/tail` 对空表定义性走同一展开形）——落加强形。

  证体要点（rotate_subdivFace0_alt，HOL 对 k 归纳的 Lean 重排）：把
  `rotate_to` 换成 `F.rotate (F.idxOf v)`（`rotateToEqRotate`）后，命题化为
  对「后缀起点 j」的下标归纳（私件 `subdivFace0AltSuffix`）：链条件
  `f.nextVertex R[j] = R[j+1]` 由 `nextVertexNextEl`（T3）+ `nextElRotate`
  （Reduction5BetwnBase，旋转下 `next_el` 函数不变）+ `nextElEl`（T54）
  供给；单步 = 私件 `subdivFace0AltSomeStep`（cons 方程 rfl + 两 if 闭合）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W2a
import Kepler.Text.Reduction1W2c
import Kepler.Text.Reduction1W2d
import Kepler.Text.Reduction3DefsSubdivAlt
import Kepler.Text.Reduction3DefsNewVertex
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList54
import Kepler.Text.Reduction5BetwnBase

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (nextEl)
open Kepler.Graphs (Face Graph makeFaceFinal replace3 splitFace split_face
  subdivFace subdivFace' generatePolygon)
open Kepler.Text.Reduction3 (subdivFace0Alt rotateTo)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq)

/-! ## §0 私件：subdivFace0_alt 的单步与后缀归纳 -/

/-- cons 步的「同步跳步」支：`f.nextVertex u = w`（且 `n = 0`）时
`subdivFace0_alt` 原样前移（HOL COND_CASES_TAC 第一支的 Lean 面）。 -/
private theorem subdivFace0AltSomeStep (g : Graph) (f : Face) (u w : ℕ)
    (vos : List (Option ℕ)) (h : f.nextVertex u = w) :
    subdivFace0Alt g f u 0 (Option.some w :: vos) =
      subdivFace0Alt g f w 0 vos := by
  have heq : subdivFace0Alt g f u 0 (Option.some w :: vos) =
      (if (Option.some w : Option ℕ) = none then subdivFace0Alt g f u (0 + 1) vos
       else if (f.nextVertex u == (Option.some w : Option ℕ).getD 0 &&
           (0 : ℕ) == 0) = true then
         subdivFace0Alt g f ((Option.some w : Option ℕ).getD 0) 0 vos
       else
         subdivFace0Alt
           (splitFace g u ((Option.some w : Option ℕ).getD 0) f
             (List.range' g.countVertices 0)).2.2
           (splitFace g u ((Option.some w : Option ℕ).getD 0) f
             (List.range' g.countVertices 0)).2.1
           ((Option.some w : Option ℕ).getD 0) 0 vos) := rfl
  rw [heq, if_neg (by simp), if_pos (by simp [h])]
  rfl

/-- **HOL `rotate_subdivFace0_alt` 证体的下标重排**：`R` 的后缀
`R.drop j`（长 `n + 1`）沿 nextVertex 链走完时 `subdivFace0_alt` 原样返回。 -/
private theorem subdivFace0AltSuffix (g : Graph) (f : Face) (R : List ℕ)
    (hchain : ∀ i (hi : i + 1 < R.length), f.nextVertex R[i] = R[i + 1]) :
    ∀ n j (hj : j + n + 1 = R.length),
      subdivFace0Alt g f R[j] 0 ((R.drop (j + 1)).map Option.some) = (f, g)
  | 0, j, hj => by
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
  | n + 1, j, hj => by
      have hj1 : j + 1 < R.length := by omega
      rw [List.drop_eq_getElem_cons hj1, List.map_cons,
        subdivFace0AltSomeStep g f R[j] R[j + 1] _ (hchain j hj1)]
      exact subdivFace0AltSuffix g f R hchain n (j + 1) (by omega)

/-! ## §1 `rotate_subdivFace0_alt`（reduction1.hl:1586-:1681） -/

/-- **HOL `rotate_subdivFace0_alt`**（reduction1.hl:1586-:1681）：
`0 < k ∧ k ≤ sizel (FST f) ∧ dropl (sizel (FST f) - k) (MAP SOME
(rotate_to (FST f) v)) = vs ∧ 3 ≤ sizel (FST f) ∧ MEM v (FST f) ∧
MEM (FST f) (fgraph g) ∧ all uniq (fgraph g) ⇒
(f,g) = subdivFace0_alt g f (the (HD vs)) 0 (TL vs)`。
七前提 HOL 原序（`good` 侧前提未出现于本件，无载体前移）。
证体：rotate 换 `F.rotate (F.idxOf v)` 后按后缀起点下标归纳
（私件 `subdivFace0AltSuffix`），链条件由 `nextVertexNextEl`（T3）+
`nextElRotate`（Reduction5BetwnBase）+ `nextElEl`（T54）供给。 -/
theorem rotateSubdivFace0Alt {k : ℕ} {vs : List (Option ℕ)} {v : ℕ} {f : Face}
    {g : Graph}
    (hk0 : 0 < k) (hkle : k ≤ f.vertices.length)
    (hvs : ((rotateTo f.vertices v).map Option.some).drop
        (f.vertices.length - k) = vs)
    (h3 : 3 ≤ f.vertices.length)
    (hv : v ∈ f.vertices)
    (hfm : f.vertices ∈ g.fgraph)
    (hun : ∀ l ∈ g.fgraph, l.Nodup) :
    (f, g) = subdivFace0Alt g f vs.head!.get! 0 vs.tail := by
  have hnd : f.vertices.Nodup := hun f.vertices hfm
  have hRlen : (rotateTo f.vertices v).length = f.vertices.length :=
    sizeRotateTo hv hnd
  have hR : rotateTo f.vertices v = f.vertices.rotate (f.vertices.idxOf v) :=
    rotateToEqRotate hv hnd
  have hRnd : (rotateTo f.vertices v).Nodup := by
    rw [hR]; exact List.nodup_rotate.mpr hnd
  have hjlt : f.vertices.length - k < (rotateTo f.vertices v).length := by
    rw [hRlen]; omega
  -- 旋转下 next_el 函数不变（先对任意 x 陈述，避开 getElem 下重写）
  have hrotAll : ∀ x, nextEl (rotateTo f.vertices v) x = nextEl f.vertices x := by
    intro x
    rw [hR]
    exact Kepler.Text.Reduction5.nextElRotate hnd _ x
  -- 链条件：R 的相邻元素互为 nextVertex
  have hchain : ∀ i (hi : i + 1 < (rotateTo f.vertices v).length),
      f.nextVertex (rotateTo f.vertices v)[i] = (rotateTo f.vertices v)[i + 1] := by
    intro i hi
    have h0 : (rotateTo f.vertices v)[i] ∈ rotateTo f.vertices v :=
      List.getElem_mem (by omega)
    have hmemF : (rotateTo f.vertices v)[i] ∈ f.vertices :=
      (memRotateTo2 hv hnd).mpr h0
    rw [Kepler.Text.TameSpine.nextVertexNextEl hmemF, ← hrotAll]
    exact Kepler.Text.TameSpine.nextElEl hRnd hi
  rw [← List.map_drop, List.drop_eq_getElem_cons hjlt, List.map_cons] at hvs
  subst hvs
  show (f, g) =
    subdivFace0Alt g f (rotateTo f.vertices v)[f.vertices.length - k] 0
      (((rotateTo f.vertices v).drop (f.vertices.length - k + 1)).map Option.some)
  exact (subdivFace0AltSuffix g f (rotateTo f.vertices v) hchain (k - 1)
    (f.vertices.length - k) (by rw [hRlen]; omega)).symm

/-! ## §2 `rotate_subdivFaceFinal`（reduction1.hl:1682-:1703，展开形） -/

/-- **HOL `rotate_subdivFaceFinal`**（reduction1.hl:1682-:1703）的
**`subdivFaceFinal` 展开形**（HOL 陈述 `subdivFaceFinal g f vs = makeFaceFinal
f g`，其定义为 `let (f,g) = subdivFace0_alt g f (the (HD vs)) 0 (TL vos) in
makeFaceFinal f g`，此处按定义内联）：
`MAP SOME (rotate_to (FST f) v) = vs ∧ 3 ≤ sizel (FST f) ∧ MEM v (FST f) ∧
MEM (FST f) (fgraph g) ∧ all uniq (fgraph g) ⇒
makeFaceFinal (subdivFace0_alt g f (the (HD vs)) 0 (TL vs)).1 (…).2 =
makeFaceFinal f g`。五前提 HOL 原序。 -/
theorem rotateSubdivFaceFinal {vs : List (Option ℕ)} {v : ℕ} {f : Face} {g : Graph}
    (hvs : (rotateTo f.vertices v).map Option.some = vs)
    (h3 : 3 ≤ f.vertices.length) (hv : v ∈ f.vertices)
    (hfm : f.vertices ∈ g.fgraph) (hun : ∀ l ∈ g.fgraph, l.Nodup) :
    makeFaceFinal (subdivFace0Alt g f vs.head!.get! 0 vs.tail).1
      (subdivFace0Alt g f vs.head!.get! 0 vs.tail).2 = makeFaceFinal f g := by
  have hkey := rotateSubdivFace0Alt (k := f.vertices.length) (vs := vs) (v := v)
    (f := f) (g := g) (by omega) (Nat.le_refl _)
    (by rw [Nat.sub_self, List.drop_zero]; exact hvs) h3 hv hfm hun
  rw [← hkey]

/-! ## §3 `subdivFaceFinal_eq`（reduction1.hl:1718-:1732，展开形） -/

/-- **HOL `subdivFaceFinal_eq`**（reduction1.hl:1718-:1732）的
**`subdivFaceFinal` 展开形**（HOL 陈述 `subdivFace g f vos = subdivFaceFinal
g f vos`，前提 `~(vos = [])`；其定义为 `let (f,g) = subdivFace0_alt g f
(the (HD vos)) 0 (TL vos) in makeFaceFinal f g`，此处按定义内联）：
`subdivFace g f vos = makeFaceFinal (subdivFace0_alt g f (the (HD vos)) 0
(TL vos)).1 (…).2`。HOL 前提 `~(vos = [])` 在 Lean 载体下不需要
（`subdivFace` 的 `head!/tail` 对空表定义性走同一展开形）——加强形；
即 `subdivFace0Final`（Reduction1W2c）的换装。 -/
theorem subdivFaceFinalEq (vos : List (Option ℕ)) (g : Graph) (f : Face) :
    subdivFace g f vos =
      makeFaceFinal (subdivFace0Alt g f vos.head!.get! 0 vos.tail).1
        (subdivFace0Alt g f vos.head!.get! 0 vos.tail).2 :=
  (subdivFace0Final g f vos.head!.get! 0 vos.tail).symm

/-! ## §4 `mem_makeFaceFinal_generatePolygon`（reduction1.hl:1733-:1781） -/

/-- **HOL `mem_makeFaceFinal_generatePolygon`**（reduction1.hl:1733-:1781）：
`3 ≤ sizel (FST f) /\ MEM v (FST f) /\ MEM (FST f) (fgraph g) /\
all uniq (fgraph g) /\ good_faces_v3 g /\
vertices_set2 g = elements_of_list (fgraph g) ==>
MEM (makeFaceFinal f g) (generatePolygon (sizel (FST f)) v f g)`。
六前提 HOL 原序（`good_faces_v3`/`vertices_set2` 载体 = TameCorrList
`GoodFacesV3`/`VerticesSet2Eq`，同 `allSomeGeneratePolygon` 既落形）。
证体（HOL 绕 `subdivFaceFinal` 中转的 Lean 直达版）：
`makeFaceFinal f g = makeFaceFinal (alt).1 (alt).2`（§2，k = 全长）=
`subdivFace g f vs`（§3 对称）∈ `generatePolygon vs.length v f g`
（`allSomeGeneratePolygon`，W2d）。
**本件绿即 `subdivFaceFinal` 定义与 `subdivFaceFinal_eq`-常量形可省的
机器证据（工单红线项）。** -/
theorem memMakeFaceFinalGeneratePolygon {f : Face} {g : Graph} {v : ℕ}
    (h3 : 3 ≤ f.vertices.length) (hv : v ∈ f.vertices)
    (hfm : f.vertices ∈ g.fgraph) (hun : ∀ l ∈ g.fgraph, l.Nodup)
    (hgf : GoodFacesV3 g) (hvs2 : VerticesSet2Eq g) :
    makeFaceFinal f g ∈ generatePolygon f.vertices.length v f g := by
  have hvs : (rotateTo f.vertices v).map Option.some =
      (rotateTo f.vertices v).map Option.some := rfl
  have hlen : ((rotateTo f.vertices v).map Option.some).length =
      f.vertices.length := by
    rw [List.length_map, rotateToBridge]
    exact sizeRotateTo hv (hun f.vertices hfm)
  have hmem := allSomeGeneratePolygon
    (vs := (rotateTo f.vertices v).map Option.some) rfl h3 hv hfm hun hgf hvs2
  rw [hlen] at hmem
  rw [subdivFaceFinalEq, rotateSubdivFaceFinal hvs h3 hv hfm hun] at hmem
  exact hmem

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.rotateSubdivFace0Alt
#print axioms Kepler.Text.Reduction1.rotateSubdivFaceFinal
#print axioms Kepler.Text.Reduction1.subdivFaceFinalEq
#print axioms Kepler.Text.Reduction1.memMakeFaceFinalGeneratePolygon
