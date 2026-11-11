/-
  Kepler.Text.Reduction3Thm14i — J5-8 W5：`main_induction`（reduction3.hl:5390-5631）。

  ┌─ 归属对账（HOL Light Flyspeck text_formalization/tame/reduction3.hl）──
  │ :5390 `main_induction` → `mainInduction`（T14 收官主件）：
  │   `assumption_setK10 ==> ∀ i L N g …,
  │      (r_trans_eq / core_split_normal_list / good_list / good_list_nodes /
  │       is_restricted / newvertex_prepped / marked_list / ¬final_list /
  │       match_quotient_list / ¬finalGraph / planegraphP / good_faces_v3 /
  │       vertices_set2 / p / fs / f / v / (r,x) / fx / uvns / gi / fi / i ≤ k)
  │      ==> fgraph gi = quotient L (ntrans i) ∧ good_faces_v3 gi ∧
  │          |faceListAt gi| = countVertices gi ∧ vertices_set2 gi = elements ∧
  │          (0 < i → SOME z_{i-1},0 = FST (b_nfgtrans0 … i)) ∧
  │          (fi,gi) = SND (b_nfgtrans0 … i) ∧ core L (rtrans i) = FST fi`。
  └────────────────────────────────────────────────────────────────

  **路线（对 i 归纳；上游 A/B/C 三簇全清 + 14j 前提包）**：
  · 0 支：`nfgtrans'Zero`/`ntrans 0 = N` 退化为初始状态；四不变量 = 给定；
    `core L r = FST f` 由 `minimalFaceCore`；`|faceListAt g| = countVertices g`
    由 `sizelFaceListAt` + `PlaneGraphPSpine p g`。
  · succ 支：`nfgtransSuc` 展开 `gi/fi` 为一次 `splitFace`，随后逐件：
      A4 `fgraphQuotientListTransform` ⇒ 第 1 条；
      C4 `goodFacesTransformLemma` + 14j `goodFacesTransformLemmaPremises` ⇒ 第 2 条；
      B5 `sizelFaceListAtSplitFace` ⇒ 第 3 条；
      B4 `splitFaceGoodVerticesSet2` ⇒ 第 4 条；
      `bNfgtransInduction`/`t12c_b_nfgtrans1` ⇒ 第 5/6 条；
      T14c `coreRtrans` ⇒ 第 7 条。
    `assumptionSetK10` 在状态 0 与状态 i 各实例化一次。

  **DIFFERS**：
  ① HOL `r_trans_eq_assumption L` ↦ 链形全称 `hrreAll` + spine 形 `hrreSAll`
    （`lnrxInductionSpine` 仅 spine 形；同 `nfgtransFst` 口径）。
  ② HOL `core_split_normal_list_assumption L` ↦ 逐状态 schema `hcsnl`。
  ③ `good_faces_v3` ↦ `TameCorrList.GoodFacesV3`；`vertices_set2 g = elements_of_list (fgraph g)`
    ↦ `VerticesSet2Eq g`；`planegraphP p g` ↦ `PlaneGraphPSpine p g`；
    `~finalGraph g` ↦ `g.final = false`。
  ④ `sizel`/`undup`/`MAP FST`/`flatten` ↦ `List.length`/`List.dedup`/
    `List.map (fun d => d.1)`/`List.flatten`；`foldr maxn 0 (MAP sizel L) - 3` ↦
    `(L.map List.length).foldr max 0 - 3`；`SOME` ↦ `some`，`PRE i` ↦ `i - 1`。
  ⑤ `AqiunppSlot` 由 `TameSpine.aqiunpp` 无条件构造，不新增前提。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm14j
import Kepler.Text.Reduction3Thm14h
import Kepler.Text.Reduction3Thm14b
import Kepler.Text.Reduction3Thm14g
import Kepler.Text.Reduction3Thm14f
import Kepler.Text.Reduction3Thm14e
import Kepler.Text.Reduction3Thm14c
import Kepler.Text.Reduction3Thm7E
import Kepler.Text.Reduction3Thm12C
import Kepler.Text.Reduction3Thm12
import Kepler.Text.Reduction3Thm13B
import Kepler.Text.T4TheoryA
import Kepler.Text.T4TheoryB
import Kepler.Text.Reduction1W4a
import Kepler.Text.TameSpine.Reduction3LnrxInductionSpine
import Kepler.Text.ChainSpineBridge
import Kepler.Text.TameSpine.Reduction3ChainFinalBridge
import Kepler.Text.Reduction3DefsAssumption
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.TameSpine.TameList58
import Kepler.Text.TameSpine.JcajyduRed2Tav2

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph fgraph between minimalFace minimalVertex nonFinals splitFace split_face)
open Kepler.Assembly (GoodList findFaceDarts prevEl nextEl)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans ytrans ztrans transformCount finalList
    rRtransEq coreSplitNormalList splitNormalList transformList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList elementsOfList)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq)

/-- **J5-8 W5：HOL `main_induction`**（reduction3.hl:5390-5631）。 -/
theorem mainInduction
    (hK10 : assumptionSetK10 GoodNodesSlot IsRestrictedSlot MarkedSlot) :
    ∀ (i : ℕ) (L : fgraph ℕ) (N : List (List Dart)) (g : Graph) (p : ℕ)
      (fs : List Face) (f : Face) (v : ℕ) (r : List Dart) (x : Dart)
      (fx : List Dart) (uvns : List (ℕ × ℕ × ℕ)) (gi : Graph) (fi : Face),
      (hL : GoodList L) →
      (hrreAll : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
        rRtransEq L N' r' y) →
      (hrreSAll : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
        Kepler.Text.TameSpine.rRtransEqSpine L N' r' y) →
      (hcsnl : ∀ (N' : List (List Dart)) (r' : List Dart) (y : Dart),
        Kepler.Text.ChainLists.markedList L hL N' r' y → ¬ finalList L r' →
        coreSplitNormalList L N' r' y) →
      GoodListNodesTl L hL →
      (hypermapOfList L hL).IsRestricted →
      newvertexPrepped L N r x →
      Kepler.Text.ChainLists.markedList L hL N r x →
      ¬ finalList L r →
      matchQuotientList g L N →
      g.final = false →
      Kepler.Text.TameSpine.PlaneGraphPSpine p g →
      GoodFacesV3 g →
      VerticesSet2Eq g →
      (L.map List.length).foldr max 0 - 3 = p →
      nonFinals g = fs →
      minimalFace fs = f →
      minimalVertex g f = v →
      loopChoice2 g L N = (r, x) →
      findFaceDarts L x = fx →
      coreTripleV4 L N r x = uvns →
      (nfgtrans' (g.countVertices, f, g) L N r x i).2.2 = gi →
      (nfgtrans' (g.countVertices, f, g) L N r x i).2.1 = fi →
      i ≤ transformCount L N r x →
      fgraphOfGraph gi = quotientList L (ntrans L N r x i) ∧
      GoodFacesV3 gi ∧
      gi.faceListAt.length = gi.countVertices ∧
      VerticesSet2Eq gi ∧
      (0 < i → ((some (ztrans L N r x (i - 1)).1, 0) : Option ℕ × ℕ) =
        (bNfgtrans0 f g L N r x i).1) ∧
      (fi, gi) = (bNfgtrans0 f g L N r x i).2 ∧
      core L (rtrans L N r x i) = fi.vertices := by
  intro i
  induction i with
  | zero =>
    intro L N g p fs f v r x fx uvns gi fi hL hrreAll hrreSAll hcsnl hgn hir hnvp hm hnf
      hmq hng hpg hgf hvs2 hp hfs hf hv hlc hfx huv hgi hfi hi
    rw [nfgtrans'Zero] at hgi hfi
    have hgi' : gi = g := hgi.symm
    have hfi' : fi = f := hfi.symm
    rw [hgi', hfi']
    have hnt0 : ntrans L N r x 0 = N := by simp [ntrans]
    have hrt0 : rtrans L N r x 0 = r := by simp [rtrans]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hnt0]; exact hmq.2
    · exact hgf
    · exact Kepler.Text.Reduction1.sizelFaceListAt ⟨p, hpg⟩
    · exact hvs2
    · intro h0; omega
    · rw [bNfgtrans0Zero]
    · rw [hrt0]
      exact minimalFaceCore L hL hgn hir N r x g hmq hm hng f v
        (by rw [hfs]; exact hf) hv.symm hlc
  | succ i ih =>
    intro L N g p fs f v r x fx uvns gi fi hL hrreAll hrreSAll hcsnl hgn hir hnvp hm hnf
      hmq hng hpg hgf hvs2 hp hfs hf hv hlc hfx huv hgi hfi hi
    have hile : i ≤ transformCount L N r x := by omega
    have hilt : i < transformCount L N r x := by omega
    -- AqiunppSlot（无条件）
    have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
      fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
    -- 状态 0 的 elementPre / 计数
    have hconv0 := Kepler.Text.Reduction3.elementsOfListVerticesSet2Converse
      L hL hm g hmq.2 hvs2
    have hpre0 : elementPre L N := hconv0.2
    -- 状态 i 的 marked / ¬final / lnrx
    have hm_i : Kepler.Text.ChainLists.markedList L hL
        (ntrans L N r x i) (rtrans L N r x i) x := haq hgn N r x hm i
    have hfi_i : ¬ finalList L (rtrans L N r x i) :=
      Kepler.Text.Reduction4.transformCount_not i hilt
    have hunL : ∀ l ∈ L, l.Nodup :=
      Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
    have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
      Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
    have htcS : Kepler.Text.TameSpine.transformCountSpine L N r x
        = transformCount L N r x := by
      rw [Kepler.Text.TameSpine.transformCountEqSpineOfAq L hL hgn haq hm hnf]
    obtain ⟨hnvp_i_sp, hpre_i_sp⟩ :=
      Kepler.Text.TameSpine.lnrxInductionSpine L hL hgn hrreAll hrreSAll hmS hnvp hpre0
        i (by rw [htcS]; exact hilt)
    have hnt_i : ntrans L N r x i = Kepler.Text.TameSpine.ntransSpine L N r x i :=
      Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm i
    have hrt_i : rtrans L N r x i = Kepler.Text.TameSpine.rtransSpine L N r x i :=
      Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i
    have hnvp_i : newvertexPrepped L (ntrans L N r x i) (rtrans L N r x i) x := by
      rw [hnt_i, hrt_i]; exact hnvp_i_sp
    have hpre_i : elementPre L (ntrans L N r x i) := by
      rw [hnt_i]; exact hpre_i_sp
    -- hcore / hprev0
    have hcore : core L r = f.vertices :=
      minimalFaceCore L hL hgn hir N r x g hmq hm hng f v
        (by rw [hfs]; exact hf) hv.symm hlc
    have hqu : ∀ s ∈ quotientList L N, s.Nodup := hm.2.2.2.2.1.1
    have hprev0 : (prevEl (core L r) v, v) = x := by
      rw [hcore]
      exact (loopChoiceProps L hL hgn hir N hm.2.1 g hng hqu hmq r x f v
        (by rw [hfs]; exact hf) hv hlc).2.2.2
    -- K10 于状态 0
    have hK0 := hK10 L N r x (transformCount L N r x) uvns
      (destTripleFull (core L r) v uvns)
      ((destTripleFull (core L r) v uvns).filterMap id) fx v
      ⟨hL, (fun _ => hgn), (fun _ => hir), hpre0, hnvp, (fun _ => hm), hnf,
       huv, rfl, rfl, rfl, hfx, hprev0⟩
    obtain ⟨k0_0, k0_1, k0_2, k0_3, k0_4, k0_5, k0_6, k0_7, k0_8, k0_9,
      k0_10, k0_11, k0_12, k0_13, k0_14, k0_15, k0_16, k0_17, k0_18, k0_19,
      k0_20, k0_21, k0_22, k0_23, k0_24, k0_25, k0_26, k0_27, k0_28, k0_29,
      k0_30, k0_31, k0_32, k0_33, k0_34, k0_35, k0_36, k0_37, k0_38, k0_39,
      k0_40, k0_41⟩ := hK0
    -- K10 于状态 i（N := ntrans i, r := rtrans i）
    have hprev_i : (prevEl (core L (rtrans L N r x i)) v, v) = x := k0_5 i hilt
    have hKi := hK10 L (ntrans L N r x i) (rtrans L N r x i) x
      (transformCount L (ntrans L N r x i) (rtrans L N r x i) x)
      (coreTripleV4 L (ntrans L N r x i) (rtrans L N r x i) x)
      (destTripleFull (core L (rtrans L N r x i)) v
        (coreTripleV4 L (ntrans L N r x i) (rtrans L N r x i) x))
      ((destTripleFull (core L (rtrans L N r x i)) v
        (coreTripleV4 L (ntrans L N r x i) (rtrans L N r x i) x)).filterMap id)
      fx v
      ⟨hL, (fun _ => hgn), (fun _ => hir), hpre_i, hnvp_i, (fun _ => hm_i), hfi_i,
       rfl, rfl, rfl, rfl, hfx, hprev_i⟩
    obtain ⟨ki_0, ki_1, ki_2, ki_3, ki_4, ki_5, ki_6, ki_7, ki_8, ki_9,
      ki_10, ki_11, ki_12, ki_13, ki_14, ki_15, ki_16, ki_17, ki_18, ki_19,
      ki_20, ki_21, ki_22, ki_23, ki_24, ki_25, ki_26, ki_27, ki_28, ki_29,
      ki_30, ki_31, ki_32, ki_33, ki_34, ki_35, ki_36, ki_37, ki_38, ki_39,
      ki_40, ki_41⟩ := hKi
    have hprevFst_i : (prevEl (rtrans L N r x i) (ztrans L N r x i)).1
        = (ztrans L N r x i).1 := by
      simpa [ztrans, ntrans, rtrans, Function.iterate_zero_apply] using ki_11
    have hsplitNF_i : core L (splitNormalList L (rtrans L N r x i) (findFaceDarts L x)
          (ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0)
          (prevEl (rtrans L N r x i) (ztrans L (ntrans L N r x i) (rtrans L N r x i) x 0))).1
          ∉ quotientList L (ntrans L N r x i) ∧
        core L (splitNormalList L (rtrans L N r x i) (findFaceDarts L x)
          (ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0)
          (prevEl (rtrans L N r x i) (ztrans L (ntrans L N r x i) (rtrans L N r x i) x 0))).2
          ∉ quotientList L (ntrans L N r x i) :=
      (by
        have h := ki_15
        dsimp only at h
        rw [← hfx] at h
        exact h)
    -- IH 于状态 i
    let p' : ℕ × Face × Graph := nfgtrans' (g.countVertices, f, g) L N r x i
    let gi' : Graph := p'.2.2
    let fi' : Face := p'.2.1
    have hIH := ih L N g p fs f v r x fx uvns gi' fi' hL hrreAll hrreSAll hcsnl hgn hir
      hnvp hm hnf hmq hng hpg hgf hvs2 hp hfs hf hv hlc hfx huv rfl rfl hile
    obtain ⟨hIH1, hIH2, hIH3, hIH4, hIH5, hIH6, hIH7⟩ := hIH
    -- nfgtransSuc 展开
    have hsucc := nfgtransSuc i (g.countVertices) f g L N r x hL hgn haq hm hnf hir hi
    rw [hsucc] at hgi hfi
    rw [subdivTripleStepPaired] at hgi hfi
    dsimp only at hgi hfi
    let newVs : List ℕ := List.range' p'.1
      (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length
    have hstep : (splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs).2.2
        = gi := hgi
    have hstepf : (splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs).2.1
        = fi := hfi
    -- nfgtransFst + hmap
    have hnfst := nfgtransFst i f g (g.countVertices) L N r x hL hgn hir haq hm hnf hnvp hpre0
      hrreAll hrreSAll hconv0.1.symm hile
    have hp1 : p'.1 = ((ntrans L N r x i).flatten.map (fun d => d.1)).dedup.length := hnfst
    have hmap : (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).map
        (fun d => d.1) = newVs := by
      have h4 := k0_4 i hilt
      rw [← hfx] at h4
      rw [← h4]
      show List.range' _ _ = newVs
      rw [← hp1]
    -- hmem / nfgtransMem
    have hfmem : f ∈ g.faces := by
      have h := Kepler.Text.TameSpine.minimalFaceFace g hng
      rwa [hfs, hf] at h
    have hIHmem : fi' ∈ gi'.faces :=
      nfgtransMem i (g.countVertices) f g L N r x hL hgn haq hm hnf hir hile hfmem
    -- ntrans (i+1) 折叠
    have hnt_succ : ntrans L N r x (i + 1)
        = ntrans L (ntrans L N r x i) (rtrans L N r x i) x 1 := by
      have hpair : (ntrans L N r x i, rtrans L N r x i)
          = (transformList L x)^[i] (N, r) := by
        simp [ntrans, rtrans]
      rw [show ntrans L N r x (i + 1) = ((transformList L x)^[i + 1] (N, r)).1 by
        simp [ntrans]]
      rw [show ntrans L (ntrans L N r x i) (rtrans L N r x i) x 1
            = (transformList L x (ntrans L N r x i, rtrans L N r x i)).1 by
        simp [ntrans]]
      rw [Function.iterate_succ_apply']
      rw [hpair]
    have hrt_succ : rtrans L N r x (i + 1)
        = rtrans L (ntrans L N r x i) (rtrans L N r x i) x 1 := by
      have hpair : (ntrans L N r x i, rtrans L N r x i)
          = (transformList L x)^[i] (N, r) := by
        simp [ntrans, rtrans]
      rw [show rtrans L N r x (i + 1) = ((transformList L x)^[i + 1] (N, r)).2 by
        simp [rtrans]]
      rw [show rtrans L (ntrans L N r x i) (rtrans L N r x i) x 1
            = (transformList L x (ntrans L N r x i, rtrans L N r x i)).2 by
        simp [rtrans]]
      rw [Function.iterate_succ_apply']
      rw [hpair]
    -- hcs（状态 i） / hnewVs' / hr1 / hr2 / hrne
    have hcs_i : coreSplitNormalList L (ntrans L N r x i) (rtrans L N r x i) x :=
      hcsnl (ntrans L N r x i) (rtrans L N r x i) x hm_i hfi_i
    have hconv_i := Kepler.Text.Reduction3.elementsOfListVerticesSet2Converse
      L hL hm_i gi' hIH1 hIH4
    have hnewVs' : List.range' gi'.countVertices
        (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length
        = newVs := by
      show List.range' gi'.countVertices _ = List.range' p'.1 _
      rw [hp1, hconv_i.1]
    have hr1 : (ytrans L N r x i).1 ∈ fi'.vertices := by
      rw [← hIH7]
      simpa only [ytrans, ntrans, rtrans, Function.iterate_zero_apply] using ki_8 0 ki_17
    have hr2 : (ztrans L N r x i).1 ∈ fi'.vertices := by
      rw [← hIH7]
      simpa only [ztrans, ntrans, rtrans, Function.iterate_zero_apply] using ki_9 0 ki_17
    have hrne : (ytrans L N r x i).1 ≠ (ztrans L N r x i).1 := by
      simpa only [ytrans, ztrans, ntrans, rtrans, Function.iterate_zero_apply] using ki_14
    have hndf : f.vertices.Nodup := by
      have hfq : f.vertices ∈ quotientList L N := by
        rw [← hmq.2]
        exact List.mem_map.mpr ⟨f, hfmem, rfl⟩
      exact hm.2.2.2.2.1.1 f.vertices hfq
    have hnot_i : ¬ (nextEl fi'.vertices (ytrans L N r x i).1 = (ztrans L N r x i).1 ∧
        (between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i)).length = 0) := by
      rw [← hIH7]
      by_cases hi00 : i = 0
      · subst hi00
        simpa only [rtrans, ← hfx, Function.iterate_zero_apply] using k0_7
      · have h := k0_10 i (Nat.pos_of_ne_zero hi00) hilt
        rw [← hfx] at h
        exact h.2.1
    -- 第 1 条：fgraph
    have hpart1 : fgraphOfGraph gi = quotientList L (ntrans L N r x (i + 1)) := by
      have h := fgraphQuotientListTransform L (ntrans L N r x i) (rtrans L N r x i) x
        gi' fi' gi newVs hL hgn hm_i hir hfi_i hIH1 hIH7 hIHmem hstep hprevFst_i hmap hcs_i
      rwa [← hnt_succ] at h
    -- 第 3 条：faceListAt 长度
    have hpart3 : gi.faceListAt.length = gi.countVertices :=
      sizelFaceListAtSplitFace gi' gi fi' newVs (ytrans L N r x i).1
        (ztrans L N r x i).1 hIH3 hstep
    -- 第 4 条：vertices_set2
    have hws : newVs.length = (between (findFaceDarts L x)
        (Kepler.Text.Reduction5.ly L (rtrans L N r x i) x)
        (Kepler.Text.Reduction5.lz L (ntrans L N r x i) (rtrans L N r x i) x)).length := by
      rw [show newVs.length = (between (findFaceDarts L x) (ytrans L N r x i)
          (ztrans L N r x i)).length from by
        rw [show newVs = List.range' p'.1 (between (findFaceDarts L x)
            (ytrans L N r x i) (ztrans L N r x i)).length from rfl, List.length_range']]
      rfl
    have hpart4 : VerticesSet2Eq gi :=
      splitFaceGoodVerticesSet2 L (ntrans L N r x i) (rtrans L N r x i) x
        (ntrans L N r x (i + 1)) gi gi' (ytrans L N r x i).1 (ztrans L N r x i).1
        fi' newVs hL hgn haq hm_i hfi_i hir
        (hrreAll (ntrans L N r x i) (rtrans L N r x i) x) hnvp_i hIH1 hnt_succ.symm
        hstep hpart1 hws hIH4
    -- 第 2 条：good_faces_v3（14j 前提包 + C4）
    have hsplit_eq : splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs
        = ((splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs).1, fi, gi) := by
      rw [← hstepf, ← hstep]
    have hprem := goodFacesTransformLemmaPremises L (ntrans L N r x i)
      (rtrans L N r x i) x gi' gi newVs v fi'
      (splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs).1 fi
      hL hgn hm_i hir hfi_i hIH2 hIHmem hIH1 hIH7 hIH3.symm hpart3.symm hIH4 hsplit_eq hmap
      hnewVs' hprevFst_i hcs_i hsplitNF_i hr1 hr2 hrne
    obtain ⟨hndF, hnf1, hnf2, hnews, hall, -, -, -⟩ := hprem
    have hpart2 : GoodFacesV3 gi :=
      goodFacesTransformLemma L (ntrans L N r x i) (rtrans L N r x i) x gi' gi newVs v
        fi' (splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs).1 fi
        hL hgn hm_i hir haq hIH2 hndF hIHmem hIH1 (by rw [← hnt_succ]; exact hpart1) hIH7
        (by rw [← hIH7]; exact hprev_i) hIH3.symm hpart3.symm hIH4 hpart4 hsplit_eq hnf1 hnf2
        hnews hmap hr1 hr2 hrne hall
    -- 第 5/6 条：b_nfgtrans0
    have hbnf : bNfgtrans0 f g L N r x (i + 1)
        = (((some (ztrans L N r x i).1), 0), fi, gi) := by
      by_cases hi0 : i = 0
      · subst hi0
        have hgi0 : gi' = g := rfl
        have hfi0 : fi' = f := rfl
        have h1 := Kepler.Text.Reduction3.t12c_b_nfgtrans1 f g L N r x newVs
          hL hgn hir hm hnf hnewVs' hndf (by rw [← hcore, hfx]; exact k0_7)
          (fun j hj => by rw [← hcore]; exact k0_8 j hj)
          (fun j hj => by rw [← hcore]; exact k0_9 j hj) k0_17
        have hstepf0 : (splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs).2.1
            = fi := by rw [← hgi0, ← hfi0]; exact hstepf
        have hstep0 : (splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs).2.2
            = gi := by rw [← hgi0, ← hfi0]; exact hstep
        have hpair0 : (splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs).2
            = (fi, gi) := by
          show ((splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs).2.1,
            (splitFace g (ytrans L N r x 0).1 (ztrans L N r x 0).1 f newVs).2.2) = (fi, gi)
          rw [hstepf0, hstep0]
        rw [Nat.zero_add, h1, hpair0]
      · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
        have hb : bNfgtrans0 f g L N r x i
            = (((some (ztrans L N r x (i - 1)).1), 0), fi', gi') := by
          show (((bNfgtrans0 f g L N r x i).1, (bNfgtrans0 f g L N r x i).2))
            = (((some (ztrans L N r x (i - 1)).1), 0), fi', gi')
          rw [← hIH5 hpos, ← hIH6]
        have h1 := bNfgtransInduction i L N r x f g newVs fi' gi' hL hgn hm hnf hir
          hndf hndF hnot_i
          (fun hne => by rw [← hIH7, ← hcore]; exact (k0_10 i hpos hilt).2.2.1 hne)
          (by rw [← hIH7, ← hcore]; exact (k0_10 i hpos hilt).2.2.2.1)
          (fun j hj => by rw [← hcore]; exact k0_8 j hj)
          (fun j hj => by rw [← hcore]; exact k0_9 j hj)
          (fun j hj => by rw [← hIH7]; exact (k0_10 i hpos hilt).2.2.2.2.2.2.1 j hj)
          (fun j hj => by rw [← hIH7]; exact (k0_10 i hpos hilt).2.2.2.2.2.2.2 j hj)
          hpos hilt hnewVs' hb
        have hpairi : (splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs).2
            = (fi, gi) := by
          show ((splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs).2.1,
            (splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs).2.2) = (fi, gi)
          rw [hstepf, hstep]
        rw [h1, hpairi]
    have hpart5 : 0 < i + 1 → ((some (ztrans L N r x (i + 1 - 1)).1, 0) : Option ℕ × ℕ)
        = (bNfgtrans0 f g L N r x (i + 1)).1 := by
      intro _
      rw [hbnf]
      simp
    have hpart6 : (fi, gi) = (bNfgtrans0 f g L N r x (i + 1)).2 := by
      rw [hbnf]
    -- 第 7 条：core
    have hnt1 : ntrans L (ntrans L N r x i) (rtrans L N r x i) x 1
        = ntrans L N r x (i + 1) := hnt_succ.symm
    have hu : (quotientList L (ntrans L N r x i)).Nodup :=
      Kepler.Text.Reduction3.t12_marked_list_uniq_quotient L hL hgn
        (ntrans L N r x i) (rtrans L N r x i) x hm_i hir
    have hm_i1 : Kepler.Text.ChainLists.markedList L hL
        (ntrans L (ntrans L N r x i) (rtrans L N r x i) x 1)
        (rtrans L (ntrans L N r x i) (rtrans L N r x i) x 1) x :=
      haq hgn (ntrans L N r x i) (rtrans L N r x i) x hm_i 1
    have hu' : (quotientList L (ntrans L (ntrans L N r x i) (rtrans L N r x i) x 1)).Nodup :=
      Kepler.Text.Reduction3.t12_marked_list_uniq_quotient L hL hgn _ _ x hm_i1 hir
    have hfg'' : fgraphOfGraph (splitFace gi' (ytrans L N r x i).1 (ztrans L N r x i).1
        fi' newVs).2.2
        = quotientList L (ntrans L (ntrans L N r x i) (rtrans L N r x i) x 1) := by
      rw [hstep, hnt1]
      exact hpart1
    have hpart7 : core L (rtrans L N r x (i + 1)) = fi.vertices := by
      have h := coreRtrans gi' (ytrans L N r x i).1 (ztrans L N r x i).1 fi' newVs
        L (ntrans L N r x i) (rtrans L N r x i) x hu hu' hL hgn haq hir hm_i hIHmem hIH7
        hIH1 hfg''
      rw [hstepf] at h
      rwa [← hrt_succ] at h
    exact ⟨hpart1, hpart2, hpart3, hpart4, hpart5, hpart6, hpart7⟩

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.mainInduction
