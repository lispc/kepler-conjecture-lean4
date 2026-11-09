/-
  Kepler.Text.Reduction3Thm5D — T5D 批：`b_nfgtransk` 装配（reduction3.hl:4442）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │   b_nfgtransk  reduction3.hl:4442 → §A bNfgtransk
  │ 此为 `b_nfgtrans` 族收口件：`SND (b_nfgtrans0 … k) = SND (subdivFace0_beta …)`。
  │ `b_nfgtrans1`(:5232) 已由 T12C 落库（`t12c_b_nfgtrans1`），不重落。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（载体/折算；语义逐字）────────────────────────────────
  │ ① `assumption_setK10`（HOL 闭 Prop）↦ `assumptionSetK10Full`
  │    （DefsAssumptionInst 三槽实例化：GoodNodesSlot/IsRestrictedSlot/
  │    MarkedSlot；D3b 批准配方）。前提槽 `element_pre L N` 由
  │    `markedListElementPre`（T13B）供给；HOL 证体首行 TYPIFY 后未再消费。
  │ ② `vertices_set2 g` ↦ `{v : ℕ | v ∈ g.vertices}`（Assembly def 定义展开，
  │    避伞 import；同 T13B 口径）。
  │ ③ `~finalGraph g` ↦ `g.final = false`；`fgraph g` ↦ `fgraphOfGraph g`；
  │    `match_quotient_list` ↦ `matchQuotientList g L N`；
  │    `FST f` ↦ `f.vertices`；`the` 不出现。
  │ ④ `core L r = f.vertices` 由 `minimalFaceCore`（T4TheoryB）供给，用于把
  │    K10 的 `(prevEl (core L r) v, v) = x` 前提与 `destTripleFull (core L r)`
  │    转写到 `f.vertices` 口径。
  │ ⑤ 无 hfinal/条件槽（K10 结论直接给 `0 < transformCount`），无语义差。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 公开件驼峰无前缀，私有件 `t5d_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm5C
import Kepler.Text.Reduction3Thm5B
import Kepler.Text.Reduction3Thm11
import Kepler.Text.T4TheoryB
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction3Thm10
import Kepler.Text.Reduction3Thm13B

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts)
open Kepler.Graphs (Face Graph between fgraph nonFinals minimalFace minimalVertex)
open Kepler.Text.Reduction5 (Dart core finalList transformCount ytrans ztrans)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList elementsOfList)
open Kepler.Text.ChainLists (markedList)

/-- 同表不同界证的 `getElem` 同值（proof irrelevance 直给；T6D 同法私有重落）。 -/
private theorem t5d_getElem_eq_of_eq {α : Type} {l₁ l₂ : List α} (h : l₁ = l₂) (i : Nat)
    (h₁ : i < l₁.length) (h₂ : i < l₂.length) : l₁[i]'h₁ = l₂[i]'h₂ := by
  subst h
  rfl

/-! ## §A `b_nfgtransk`（reduction3.hl:4442） -/

/-- HOL `b_nfgtransk`（reduction3.hl:4442）：
`SND (b_nfgtrans0 f g L N r x k) = SND (subdivFace0_beta g f NONE 0 vs)`。

装配路线：`b_nfgtrans0` 展开 + `batch_k`（batch0 = dest_triple0）后，两侧
都是对同一 `dest_triple0` 段的 foldl；`subdiv_face0_beta` 侧再展开
`dest_triple_full` 为 初段 ++ 中段 ++ 末段，初段经
`subdivSingleStepInitialSeg` 归约到 `b_nfgtrans0` 的首态（`cond_pair` 对齐
`fst_u0`），中段由前提 ∃ 的 foldl 等式直接代入，末段经
`subdivSingleStepFinalSeg`（`f0.vertices` 上的 betwn 等式由 ∃ 的条件支供给）
收口。两侧 `.2` 同为 `(f0, g0)`。 -/
theorem bNfgtransk
    (L : fgraph ℕ) (N : List (List Dart)) (g : Graph) (fs : List Face)
    (f : Face) (v k : ℕ) (r : List Dart) (x : Dart) (fx : List Dart)
    (uvns : List (ℕ × ℕ × ℕ)) (vs : List (Option ℕ))
    (hobj : ∃ (f0 : Face) (g0 : Graph),
      (let fst_u0 : Option ℕ :=
         if (nextEl fx x).1 = (ytrans L N r x 0).1 then none
         else some (prevEl f.vertices (ytrans L N r x 0).1)
       (((some (ztrans L N r x (k - 1)).1, 0), f0, g0) =
         List.foldl subdivSingleStep ((fst_u0, 0), f, g)
           (destTriple0 f.vertices [] (coreTripleV4 L N r x)))) ∧
      f0.vertices.Nodup ∧
      x.1 ∈ f0.vertices ∧
      (ztrans L N r x (k - 1)).1 ∈ f0.vertices ∧
      ((ztrans L N r x (k - 1)).1 ≠ x.1 →
        between f0.vertices (ztrans L N r x (k - 1)).1 x.1 =
        between f.vertices (ztrans L N r x (k - 1)).1 x.1))
    (hK10 : assumptionSetK10Full)
    (hgood : GoodList L) (hnodes : GoodListNodesTl L hgood)
    (hres : (hypermapOfList L hgood).IsRestricted)
    (hprep : newvertexPrepped L N r x)
    (hmarked : markedList L hgood N r x)
    (hnfin : ¬ finalList L r)
    (hmq : matchQuotientList g L N) (hgnf : g.final = false)
    (hv2 : {w : ℕ | w ∈ g.vertices} = elementsOfList (fgraphOfGraph g))
    (hfs : fs = nonFinals g) (hf : minimalFace fs = f)
    (hv : v = minimalVertex g f) (hlc : loopChoice2 g L N = (r, x))
    (hpx : (prevEl f.vertices v, v) = x)
    (huvns : uvns = coreTripleV4 L N r x)
    (hvs : vs = destTripleFull f.vertices v uvns)
    (hk : k = transformCount L N r x) (hfx : fx = findFaceDarts L x) :
    (bNfgtrans0 f g L N r x k).2 = (subdivFace0Beta g f none 0 vs).2 := by
  -- 0. core = f.vertices（minimalFaceCore，非 J2）
  have hcore_eq : core L r = f.vertices :=
    minimalFaceCore L hgood hnodes hres N r x g hmq hmarked hgnf f v
      (by rw [← hfs]; exact hf) hv hlc
  -- 1. K10 前提槽：element_pre（T13B）+ 三载体实例化 → set3
  have hpre : elementPre L N := markedListElementPre L hgood hmarked g hmq.2 hv2
  have h3 := assumptionSet3_of_assumptionSetK10 GoodNodesSlot IsRestrictedSlot MarkedSlot
    hK10 L N r x k uvns vs (vs.filterMap id) fx v
    ⟨hgood, (fun _ => hnodes), (fun _ => hres), hprep, (fun _ => hmarked), hpre,
     hnfin, huvns.symm, (by rw [hcore_eq]; exact hvs.symm), rfl, hk.symm, hfx.symm,
     (by rw [hcore_eq]; exact hpx)⟩
  obtain ⟨_, hposK, _, _, _, _, _, _, _, _, _, hnextmem, _, hzmem, hymem, _, _, _,
    hcorend, hnextv, hcoreof, _, _, _, _, _⟩ := h3
  -- 2. 基本事实
  have hk0 : transformCount L N r x ≠ 0 := Nat.ne_of_gt hposK
  have hkpos : 0 < k := by rw [hk]; exact hposK
  have hnd : f.vertices.Nodup := hcore_eq ▸ hcorend
  have hvcore : v ∈ core L r := by rw [← hnextv]; exact hcoreof _ hnextmem
  have hvmem : v ∈ f.vertices := by rw [← hcore_eq]; exact hvcore
  have hlen : uvns.length = transformCount L N r x := by
    rw [huvns, coreTripleV4_length]
  have hne_uvns : uvns ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
    omega
  have hheadD : uvns.headD (0, 0, 0) = uvns[0]'(by rw [hlen]; exact hposK) := by
    cases uvns with
    | nil => exact absurd rfl hne_uvns
    | cons a t => rfl
  have h0uvns : uvns[0]'(by rw [hlen]; exact hposK)
      = ((ytrans L N r x 0).1, (ztrans L N r x 0).1,
         (between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0)).length) :=
    (t5d_getElem_eq_of_eq huvns 0
      (by rw [hlen]; exact hposK)
      (by rw [coreTripleV4_length]; exact hposK)).trans (elCoreTriple L N r x 0 hposK)
  have hhead : (uvns.headD (0, 0, 0)).1 = (ytrans L N r x 0).1 := by
    rw [hheadD, h0uvns]
  have humem : (ytrans L N r x 0).1 ∈ f.vertices := by
    have hy0 : ytrans L N r x 0 ∈ r := hymem 0 hkpos
    have hc : (ytrans L N r x 0).1 ∈ core L r := hcoreof _ hy0
    rw [← hcore_eq]
    exact hc
  have hx1 : x.1 = prevEl f.vertices v := (congrArg Prod.fst hpx).symm
  -- 3. 解 ∃
  obtain ⟨f0, g0, hfold, hnodup0, hx0, hv''0, hbet⟩ := hobj
  -- 4. 首态对齐（cond_pair + 取消 hnextv/hhead）
  have hstart : (if v = (uvns.headD (0, 0, 0)).1 then ((none, 0), f, g)
        else ((some (prevEl f.vertices (uvns.headD (0, 0, 0)).1), 0), f, g))
      = (((if (nextEl fx x).1 = (ytrans L N r x 0).1 then none
            else some (prevEl f.vertices (ytrans L N r x 0).1)), 0), f, g) := by
    rw [hhead, ← hnextv]
    rw [condPair, condPair]
  -- 5. 主装配
  unfold bNfgtrans0
  dsimp only
  rw [batchK f.vertices L N r x k hk, ← hfx]
  rw [subdivFace0BetaFoldlStepsAlt g f none 0 vs]
  rw [hvs]
  unfold destTripleFull
  dsimp only
  rw [List.foldl_append, List.foldl_append]
  rw [subdivSingleStepInitialSeg f g ((uvns.headD (0, 0, 0)).1) v hnd hvmem (hhead.symm ▸ humem)]
  rw [hstart]
  rw [huvns]
  rw [← hfold]
  -- 6. 末段：lastCoreTriple + x.1 = prevEl + hbet 转 f0 口径 + finalSeg
  rw [lastCoreTriple L N r x (k - 1) hk0 (by rw [hk])]
  rw [← hx1]
  have hfinseg : (if (ztrans L N r x (k - 1)).1 = x.1 then []
        else (between f.vertices (ztrans L N r x (k - 1)).1 x.1).map some
          ++ [some x.1])
      = (if (ztrans L N r x (k - 1)).1 = x.1 then []
        else (between f0.vertices (ztrans L N r x (k - 1)).1 x.1).map some
          ++ [some x.1]) := by
    by_cases hc : (ztrans L N r x (k - 1)).1 = x.1
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, ← hbet hc]
  rw [hfinseg,
    subdivSingleStepFinalSeg f0 g0 x.1 (ztrans L N r x (k - 1)).1
      hnodup0 hx0 hv''0]

/-- HOL `nfgtrans_transform_count`（reduction3.hl:4314；T11 曾判 BLOCKED，
本批经 `subdivFace0Alt2`（patch A）+ `subdivFace0Alt2FoldlStepsAlt`（T5B）解锁）：
`transform_count = k ⇒ SND (nfgtrans' (n,f,g) L N r x k) =
subdivFace0Alt2 g f n (core_triple_v4 L N r x)`。
HOL 的 `is_restricted` 前提在证体未消费（`take_oversize` + `size_core_triple`
即足），作载体参数保留。 -/
theorem nfgtransTransformCount
    (n : ℕ) (f : Face) (g : Graph) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ)
    (IsRestrictedL : fgraph ℕ → Prop) (hres : IsRestrictedL L)
    (hk : transformCount L N r x = k) :
    (nfgtrans' (n, f, g) L N r x k).2 =
      subdivFace0Alt2 g f n (coreTripleV4 L N r x) := by
  rw [subdivFace0Alt2FoldlStepsAlt g f n (coreTripleV4 L N r x)]
  unfold nfgtrans'
  rw [show (coreTripleV4 L N r x).take k = coreTripleV4 L N r x from by
    rw [← hk, ← coreTripleV4_length, List.take_length]]

end Kepler.Text.Reduction3

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.Reduction3.bNfgtransk
#print axioms Kepler.Text.Reduction3.nfgtransTransformCount
