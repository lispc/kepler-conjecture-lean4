/-
  Kepler.Text.Reduction3Thm15 — J5-8 W6a+W6b（reduction3.hl:265 / :566 / :592 / :1268 / :1322）。

  ┌─ 件目（5 件）─────────────────────────────────────────────────
  │ W6a-1 AQ6_INDUCT              :265  → aq6Induct
  │ W6a-2 ntrans_final_list1      :566  → ntransFinalList1
  │ W6a-3 ntrans_final_list       :592  → ntransFinalList
  │ W6b-1 mem_core_triple_minimalFace :1268 → memCoreTripleMinimalFace
  │ W6b-2 dest_triple_full_all_filter :1322 → destTripleFullAllFilter
  └────────────────────────────────────────────────────────────────

  **在库供料（零重落）**：
  · `TameSpine.aqiunpp`（AQIUNPP 无条件链形）；
  · `Reduction5.ntrans1` / `elementInNtransSuc` / `t10b_not_uniq_replace`
    / `TameSpine.uniqFlatten`；
  · `elCoreTriple`（Reduction3Thm3）/ `destTriple0Mem`（同）；
  · `pnxvwfs1` / `pnxvwfs2`（Reduction5J5Pnxvwfs）/ `memCore`（Reduction5McCore）；
  · `minimalFaceCore`（T4TheoryB）/ `minimalFaceNonnil`（T4TheoryA）；
  · `memMinimalVertex`（TameList58）/ `betwnMem`（Reduction5BetwnBase）
    / `prevEl_mem_of_mem`（TameLp）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction3Thm3
import Kepler.Text.Reduction3Thm10B
import Kepler.Text.Reduction5J5IdxSplit
import Kepler.Text.Reduction5J5Pnxvwfs
import Kepler.Text.Reduction5McCore
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.T4TheoryA
import Kepler.Text.T4TheoryB
import Kepler.Text.TameSpine.TameList58
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.TameSpine.JcajyduRed2Tav2

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Graphs (Face Graph between fgraph minimalFace minimalVertex nonFinals)
open Kepler.Assembly (GoodList findFaceDarts prevEl)
open Kepler.Text.Reduction5
  (Dart core quotientList ntrans rtrans ytrans ztrans transformCount finalList
    splitNormalList transformList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-! ## §W6a-1 `AQ6_INDUCT`（reduction3.hl:265） -/

/-- HOL `AQ6_INDUCT`（reduction3.hl:265）：
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x ⇒
 MEM (rtrans L N r x i) (ntrans L N r x i)`。 -/
theorem aq6Induct (i : ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hm : markedList L hL N r x) :
    rtrans L N r x i ∈ ntrans L N r x i :=
  (Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i).2.2.1

/-! ## §W6a-2 `ntrans_final_list1`（reduction3.hl:566） -/

/-- HOL `ntrans_final_list1`（reduction3.hl:566）：
`good_list ∧ good_list_nodes ∧ marked_list ∧ ¬final_list ∧ f ≠ r ∧ f ∈ N ⇒
 f ≠ rtrans 1 ∧ f ∈ ntrans 1`。 -/
theorem ntransFinalList1 (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (f : List Dart)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hne : f ≠ r) (hfN : f ∈ N) :
    f ≠ rtrans L N r x 1 ∧ f ∈ ntrans L N r x 1 := by
  have hm1 : markedList L hL (ntrans L N r x 1) (rtrans L N r x 1) x :=
    Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm 1
  have hnd : (ntrans L N r x 1).Nodup :=
    Kepler.Text.TameSpine.uniqFlatten hm1.2.1.1 hm1.2.1.2.1
  have hnt1 := Kepler.Text.Reduction5.ntrans1 L N r x hnf
  have hrt1 : rtrans L N r x 1 =
      (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
        (Kepler.Text.Reduction5.ly L r x)
        (prevEl r (Kepler.Text.Reduction5.lz L N r x))).2 := by
    simp [rtrans, transformList, hnf]
  refine ⟨?_, Kepler.Text.Reduction5.elementInNtransSuc L hL hgn hm hfN hne⟩
  intro heq
  have hf2eq : f = (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x)
      (prevEl r (Kepler.Text.Reduction5.lz L N r x))).2 := heq.trans hrt1
  have hf2N : (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x)
      (prevEl r (Kepler.Text.Reduction5.lz L N r x))).2 ∈ N := by
    rw [← hf2eq]; exact hfN
  have hne2 : (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x)
      (prevEl r (Kepler.Text.Reduction5.lz L N r x))).2 ≠ r := by
    intro h
    exact hne (hf2eq.trans h)
  have hrep := Kepler.Text.Reduction3.t10b_not_uniq_replace hm.2.2.1 hf2N hne2.symm
  rw [hnt1] at hnd
  exact hrep (List.nodup_append.mp hnd).1

/-! ## §W6a-3 `ntrans_final_list`（reduction3.hl:592） -/

/-- HOL `ntrans_final_list`（reduction3.hl:592）：
`… ∧ f ∈ N ∧ k ≤ transform_count ⇒ f ≠ rtrans k ∧ f ∈ ntrans k`（对 k 归纳）。 -/
theorem ntransFinalList (k : ℕ) (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (f : List Dart)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hne : f ≠ r) (hfN : f ∈ N) (hk : k ≤ transformCount L N r x) :
    f ≠ rtrans L N r x k ∧ f ∈ ntrans L N r x k := by
  induction k with
  | zero =>
    simp only [ntrans, rtrans, Function.iterate_zero_apply]
    exact ⟨hne, hfN⟩
  | succ k ih =>
    obtain ⟨hne_k, hfN_k⟩ := ih (by omega)
    have hmk : markedList L hL (ntrans L N r x k) (rtrans L N r x k) x :=
      Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm k
    have hnf_k : ¬ finalList L (rtrans L N r x k) :=
      Kepler.Text.Reduction4.transformCount_not k (by omega)
    have h1 := ntransFinalList1 L (ntrans L N r x k) (rtrans L N r x k) x f
      hL hgn hmk hnf_k hne_k hfN_k
    have ht := Kepler.Text.Reduction3.transAdd L N r x k 1
    refine ⟨?_, ?_⟩
    · intro h
      apply h1.1
      simpa only [show k + 1 = 1 + k from by omega, ht.2.1] using h
    · rw [show k + 1 = 1 + k from by omega, ht.1]
      exact h1.2

/-! ## §W6b-1 `mem_core_triple_minimalFace`（reduction3.hl:1268） -/

/-- HOL `mem_core_triple_minimalFace`（reduction3.hl:1268）：
`uvn ∈ core_triple_v4 L N r x ⇒ FST uvn ∈ FST f ∧ FST (SND uvn) ∈ FST f`
（f = minimalFace (nonFinals g)）。 -/
theorem memCoreTripleMinimalFace (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (g : Graph) (fs : List Face) (f : Face)
    (v : ℕ) (uvns : List (ℕ × ℕ × ℕ)) (uvn : ℕ × ℕ × ℕ)
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hng : g.final = false) (hfs : nonFinals g = fs)
    (hf : minimalFace fs = f) (hv : v = minimalVertex g f)
    (hlc : loopChoice2 g L N = (r, x))
    (hmq : matchQuotientList g L N)
    (huv : uvns = coreTripleV4 L N r x)
    (hmem : uvn ∈ uvns) :
    uvn.1 ∈ f.vertices ∧ uvn.2.1 ∈ f.vertices := by
  subst huv
  obtain ⟨j, hj, hval⟩ := List.mem_iff_getElem.mp hmem
  have hjlt : j < transformCount L N r x := by
    rw [← coreTripleV4_length]; exact hj
  have hel := elCoreTriple L N r x j hjlt
  have hEq : uvn = ((ytrans L N r x j).1, (ztrans L N r x j).1,
      (between (findFaceDarts L x) (ytrans L N r x j) (ztrans L N r x j)).length) := by
    rw [← hval]
    simpa only using hel
  rw [hEq]
  have hnfj : ¬ finalList L (rtrans L N r x j) :=
    Kepler.Text.Reduction4.transformCount_not j hjlt
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i
  have hyr : ytrans L N r x j ∈ r :=
    Kepler.Text.Reduction5.pnxvwfs1 L hL hgn haq j hnfj hm
  have hzr : ztrans L N r x j ∈ r :=
    Kepler.Text.Reduction5.pnxvwfs2 L hL hgn haq j hnfj hm
  have hyc : (ytrans L N r x j).1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore hL hgn hm hyr hnf
  have hzc : (ztrans L N r x j).1 ∈ core L r :=
    Kepler.Text.Reduction5.memCore hL hgn hm hzr hnf
  have hcore : core L r = f.vertices :=
    minimalFaceCore L hL hgn hir N r x g hmq hm hng f v
      (by rw [hfs]; exact hf) hv hlc
  rw [hcore] at hyc hzc
  exact ⟨hyc, hzc⟩

/-! ## §W6b-2 `dest_triple_full_all_filter`（reduction3.hl:1322） -/

/-- HOL `dest_triple_full_all_filter`（reduction3.hl:1322）：
`vs = dest_triple_full (FST f) v uvns ⇒
 all (λt. MEM t (FST f)) (MAP the (filter isSome vs))`。 -/
theorem destTripleFullAllFilter (L : fgraph ℕ) (N : List (List Dart))
    (r : List Dart) (x : Dart) (g : Graph) (fs : List Face) (f : Face)
    (v : ℕ) (uvns : List (ℕ × ℕ × ℕ)) (vs : List (Option ℕ))
    (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hir : (hypermapOfList L hL).IsRestricted)
    (hm : markedList L hL N r x)
    (hmq : matchQuotientList g L N)
    (hnf : ¬ finalList L r) (hng : g.final = false)
    (hfs : nonFinals g = fs) (hf : minimalFace fs = f)
    (hv : v = minimalVertex g f)
    (hlc : loopChoice2 g L N = (r, x))
    (huv : uvns = coreTripleV4 L N r x)
    (hvs : vs = destTripleFull f.vertices v uvns) :
    ∀ t ∈ vs.filterMap id, t ∈ f.vertices := by
  subst huv
  subst hvs
  -- f.vertices 非空 / v ∈ f.vertices
  have hfvne : f.vertices ≠ [] := by
    rw [← hf, ← hfs]
    exact minimalFaceNonnil L hL hgn hir N hm.2.1 g hmq hng
  have hvmem : v ∈ f.vertices := by
    rw [hv]
    exact Kepler.Text.TameSpine.memMinimalVertex g f hfvne
  -- 逐项三元的端点都在 f.vertices（W6b-1）
  have huvmem : ∀ uvn ∈ coreTripleV4 L N r x,
      uvn.1 ∈ f.vertices ∧ uvn.2.1 ∈ f.vertices :=
    fun uvn hu => memCoreTripleMinimalFace L N r x g fs f v
      (coreTripleV4 L N r x) uvn hL hgn hir hm hnf hng hfs hf hv hlc hmq rfl hu
  intro t ht
  obtain ⟨o, ho, hget⟩ := List.mem_filterMap.mp ht
  cases o with
  | none => simp at hget
  | some w =>
    injection hget with hwt
    rw [← hwt]
    have hw : some w ∈ destTripleFull f.vertices v (coreTripleV4 L N r x) := ho
    simp only [destTripleFull] at hw
    rw [List.mem_append, List.mem_append] at hw
    rcases hw with (hinit | hdt) | hfin
    · -- initialSeg
      split at hinit
      · exact absurd hinit List.not_mem_nil
      · rename_i hvu
        rcases List.mem_cons.mp hinit with hwv | hwb
        · injection hwv with hwv
          subst hwv
          exact hvmem
        · obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hwb
          injection hzw with hzw
          subst hzw
          exact Kepler.Text.Reduction5.betwnMem hz
    · -- destTriple0
      have hokS : ∀ y ∈ ([] : List (Option ℕ)), y.isSome → y.getD 0 ∈ f.vertices :=
        fun y hy => absurd hy List.not_mem_nil
      exact destTriple0Mem (coreTripleV4 L N r x) f.vertices [] (some w)
        hokS huvmem (by rfl) hdt
    · -- finalSeg
      split at hfin
      · exact absurd hfin List.not_mem_nil
      · rename_i hv'u0
        rw [List.mem_append] at hfin
        rcases hfin with hb | hu0
        · obtain ⟨z, hz, hzw⟩ := List.mem_map.mp hb
          injection hzw with hzw
          subst hzw
          exact Kepler.Text.Reduction5.betwnMem hz
        · rw [List.mem_singleton] at hu0
          injection hu0 with hu0
          subst hu0
          exact Kepler.Text.TameLp.prevEl_mem_of_mem hvmem

end Kepler.Text.Reduction3

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction3.aq6Induct
#print axioms Kepler.Text.Reduction3.ntransFinalList1
#print axioms Kepler.Text.Reduction3.ntransFinalList
#print axioms Kepler.Text.Reduction3.memCoreTripleMinimalFace
#print axioms Kepler.Text.Reduction3.destTripleFullAllFilter
