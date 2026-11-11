/-
  Kepler.Text.Reduction5J5SxC — SX-c 链（HOL reduction4.hl:3388–3752 缺件段）

  ┌─ 缺件 × HOL 锚 × 本件落点 ─────────────────────────────────────
  │ list_of_darts_quotient_flatten  :3388  ← memFlattenOfQuotDart（链形）
  │ mem_list_of_darts_quotient_core :3412  ← memListOfDartsQuotientCore（链形）
  │ non_r_darts_trans               :3433  ← nonRDartsTrans（97 HOL 行主体）
  │ non_r_darts_trans_i             :3530  ← nonRDartsTransI（迭代）
  │ list_of_darts_mem               :3563  ← listOfDartsMem（0 实例）
  │ list_of_darts_reduction 第三合取 :3694  ← k3Sx3SlotInstance（消槽）
  └────────────────────────────────────────────────────────────────

  替位（树内已在库，零新数学）：
  - `TameSpine.memListOfDartsQuotient`/`listOfDartsQuotient`（spine）→ 链形
    `memListOfDartsQuotientChain`（parts_eq_partsSpine + quotientList_eq_quotationListSpine）；
  - `TameSpine.listPairsCore`（spine）→ 链形 `listPairsCoreChain`；
  - `TameSpine.aq1b_split2Mem`（split.2 成员二分：∈ r 或 ∉ N.flatten）→ 链形
    `split2MemChain`（splitNormalListEqSpine + lyEqSpine + lzEqSpine）；
  - `Reduction5.mem_listPairs_nextEl`（list_pairs → nextEl）；
  - `Reduction5.memYRtrans1`、`Reduction4Idx.elementInNtransSuc`、
    `Reduction5.nextCoreNeFST`、`Reduction5.nextElCoreLast`、
    `Reduction4Idx.memFstCore`/`markedListUniqCore`、`Reduction4.coreiReduction`、
    `Reduction5.finalAssumptionsNotNextCore0I`、`Reduction5.betwnCoreReductionLemma`、
    `Reduction3.rtrans1`、`Reduction3.transAdd`、`Reduction3.transformCountAdd`。

  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction5J5K4Lemma
import Kepler.Text.Reduction5J5K4N1
import Kepler.Text.Reduction5J5BetwnNil
import Kepler.Text.Reduction5J5IdxSplit
import Kepler.Text.Reduction5J5CoreLast
import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.Reduction5J5FstNe
import Kepler.Text.Reduction5J5NotNextCore0I
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction4K4C1
import Kepler.Text.Reduction4
import Kepler.Text.Reduction3Thm1
import Kepler.Text.Reduction3Thm2
import Kepler.Text.Reduction5McCore
import Kepler.Text.Reduction5Ml1W5bFwd
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList58
import Kepler.Text.TameSpine.TameList59
import Kepler.Text.TameSpine.JcajyduAqLeaf1B
import Kepler.Text.TameSpine.Reduction3ChainFinalBridge
import Kepler.Text.ChainSpineBridge
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList markedList)

/-! ## §0 小机器 -/

/-- `headD (0,0) = head!`（非空表；Dart 专用私有件）。 -/
private theorem headDBangEq {l : List Dart} (hne : l ≠ []) :
    l.headD (0, 0) = l.head! := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- `p.getLast! ∈ p`（非空表）。 -/
private theorem getLastBangMem {l : List Dart} (hne : l ≠ []) : l.getLast! ∈ l :=
  Kepler.Graphs.getLast!_mem hne

/-- `[z] ++ (q ++ [y])` 的环上后继（`nextEl` 在末元回卷到首元）。 -/
private theorem nextElCatLastHead (z y : Dart) (q : List Dart)
    (hnd : ([z] ++ (q ++ [y])).Nodup) :
    nextEl ([z] ++ (q ++ [y])) y = z := by
  have hne : [z] ++ (q ++ [y]) ≠ [] := by simp
  have hlast : ([z] ++ (q ++ [y])).getLast hne = y := by
    rw [List.getLast_append_of_right_ne_nil _ _ (by simp : q ++ [y] ≠ [])]
    simp
  have hhead : ([z] ++ (q ++ [y])).headD z = z := rfl
  have h := Kepler.Text.MoreLemma2Naming.nextElLastHd (x := z) hnd hne
  rw [hlast, hhead] at h
  simpa only [nextElInstEq] using h

/-! ## §1 quotient 的 `parts`/`getLast!` 形与 core 的 `listPairs` 形（链形） -/

/-- **HOL `list_pairs_core`**（tame_list.hl:14057）：链形。
`normal_list ∧ edgeNondeg ∧ all uniq ∧ MEM r N ⇒ list_pairs (core L r) =
MAP LAST (parts L r)`。 -/
theorem listPairsCoreChain (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {r : List Dart} (hr : r ∈ N) :
    listPairs (core L r) = (parts L r).map (fun q => q.getLast!) := by
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hN
  have hcore : core L r = Kepler.Text.TameSpine.coreSpine L r := by
    show (parts L r).map (fun l => (l.headD (0, 0)).1)
      = (Kepler.Text.TameSpine.partsSpine L r).map (fun a => a.head!.1)
    rw [Kepler.Text.ChainBridge.parts_eq_partsSpine]
    exact List.map_congr_left (fun p hp => by
      rw [headDBangEq (Kepler.Text.MoreLemma2Island2.partsAllNonnil L r p
        (by rwa [← Kepler.Text.ChainBridge.parts_eq_partsSpine] at hp))])
  have h := Kepler.Text.TameSpine.listPairsCore L hL hnS hnedg hunL hr
  rw [hcore, Kepler.Text.ChainBridge.parts_eq_partsSpine]
  exact h

/-- **HOL `mem_list_of_darts_quotient`**（tame_list.hl:6913）链形：
`MEM d (list_of_darts (quotient_list L N)) ↔ ∃ p r, MEM p (parts L r) ∧ MEM r N ∧ d = LAST p`。 -/
theorem memListOfDartsQuotientChain (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) (d : Dart) :
    d ∈ listOfDarts (quotientList L N) ↔
      ∃ p : List Dart, ∃ r : List Dart,
        p ∈ parts L r ∧ r ∈ N ∧ d = p.getLast! := by
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hN
  rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine L N]
  rw [Kepler.Text.TameSpine.memListOfDartsQuotient L hL hnS hnedg hunL d]
  constructor
  · rintro ⟨p, r, hp, hr, hd⟩
    refine ⟨p, r, ?_, hr, hd⟩
    rwa [← Kepler.Text.ChainBridge.parts_eq_partsSpine] at hp
  · rintro ⟨p, r, hp, hr, hd⟩
    refine ⟨p, r, ?_, hr, hd⟩
    rwa [Kepler.Text.ChainBridge.parts_eq_partsSpine] at hp

/-- **HOL `mem_list_of_darts_quotient_core`**（reduction4.hl:3412）链形：
`MEM u (list_of_darts (quotient_list L N)) ⇒ ∃ r ∈ N, MEM u (list_pairs (core L r))`。 -/
theorem memListOfDartsQuotientCore (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {u : Dart}
    (hu : u ∈ listOfDarts (quotientList L N)) :
    ∃ r ∈ N, u ∈ listPairs (core L r) := by
  obtain ⟨p, r, hp, hr, hd⟩ :=
    (memListOfDartsQuotientChain L hL hN hnedg hunL u).mp hu
  refine ⟨r, hr, ?_⟩
  rw [listPairsCoreChain L hL hN hnedg hunL hr]
  exact List.mem_map.mpr ⟨p, hp, hd.symm⟩

/-- **HOL `list_of_darts_quotient_flatten`**（reduction4.hl:3388）链形：
`MEM u (list_of_darts (quotient_list L N)) ⇒ MEM u (flatten N)`。 -/
theorem memFlattenOfQuotDart (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {u : Dart}
    (hu : u ∈ listOfDarts (quotientList L N)) : u ∈ N.flatten := by
  obtain ⟨p, r, hp, hr, hd⟩ :=
    (memListOfDartsQuotientChain L hL hN hnedg hunL u).mp hu
  obtain ⟨_, _, _, hpne, hsub⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN hr hp
  rw [hd]
  exact List.mem_flatten.mpr ⟨r, hr, hsub _ (getLastBangMem hpne)⟩

/-- **HOL `mem_list_pairs_core`**（reduction4.hl:3360）链形：
`MEM u (list_pairs (core L r)) ⇒ MEM u r`。 -/
theorem memListPairsCoreImpMemR (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup) {r : List Dart} (hr : r ∈ N) {u : Dart}
    (hu : u ∈ listPairs (core L r)) : u ∈ r := by
  rw [listPairsCoreChain L hL hN hnedg hunL hr] at hu
  obtain ⟨p, hp, hpu⟩ := List.mem_map.mp hu
  obtain ⟨_, _, _, hpne, hsub⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN hr hp
  rw [← hpu]
  exact hsub _ (getLastBangMem hpne)

/-- **HOL `next_el_core_list_pairs`**（reduction4.hl:1647）链形（逆向）：
`u1 ∈ core L r ∧ next_el (core L r) u1 = v1 ⇒ (u1, v1) ∈ list_pairs (core L r)`。 -/
theorem memListPairsCoreOfNextEl (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    {N : List (List Dart)} (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    (hcu : (core L r).Nodup) {u1 v1 : ℕ}
    (hu1 : u1 ∈ core L r) (hnext : nextEl (core L r) u1 = v1) :
    (u1, v1) ∈ listPairs (core L r) := by
  unfold core at hu1
  obtain ⟨p, hp, hphead⟩ := List.mem_map.mp hu1
  have hpne : p ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r p hp
  have hhead : p.head!.1 = u1 := by
    rw [← hphead]
    exact (congrArg Prod.fst (headDBangEq hpne)).symm
  have hglmem : p.getLast! ∈ p := getLastBangMem hpne
  have hgl : (p.getLast!).1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hr hp hglmem
  have hlast := Kepler.Text.Reduction5.nextElCoreLast L hL hgn hunL hnedg hN hr hcu hp
  have hv : v1 = (p.getLast!).2 := by
    rw [← hnext, ← hhead, ← hgl]
    exact hlast
  rw [listPairsCoreChain L hL hN hnedg hunL hr]
  refine List.mem_map.mpr ⟨p, hp, ?_⟩
  exact Prod.ext (by rw [hgl, hhead]) (by rw [hv])

/-! ## §2 `split.2` 成员二分（链形包装，HOL `has_snd_norm_list_fliter` 替位） -/

/-- **HOL `list_of_darts_mem` 的 split 二分内核**（AQ1.hl:527 `has_snd_norm_list_fliter`
的链形替位）：`MEM d (SND split) ⇒ MEM d r ∨ ¬ MEM d (flatten N)`。 -/
theorem split2MemChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hf : ¬ finalList L r) {d : Dart}
    (hd : d ∈ (splitNormalList L r (findFaceDarts L (ly L r x))
      (ly L r x) (prevEl r (lz L N r x))).2) :
    d ∈ r ∨ d ∉ N.flatten := by
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have hfS : ¬ Kepler.Text.TameSpine.finalListSpine L r := hf
  have hd' : d ∈ (Kepler.Text.TameSpine.splitNormalListSpine L r
      (findFaceDarts L (Kepler.Text.TameSpine.lYSpine L r x))
      (Kepler.Text.TameSpine.lYSpine L r x)
      (prevEl r (Kepler.Text.TameSpine.lZSpine L N r x))).2 := by
    rw [← Kepler.Text.ChainSpineBridge.splitNormalListEqSpine]
    rw [← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hf]
    rw [← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hf]
    exact hd
  exact Kepler.Text.TameSpine.aq1b_split2Mem L hL hgn hunL hmS hfS hd'

/-! ## §3 `non_r_darts_trans`（HOL reduction4.hl:3433，97 HOL 行主体） -/

/-- **HOL `non_r_darts_trans`**（reduction4.hl:3433）：
`u` 在 quotient N 中但不在 `core r` 中 ⇒ 一步后仍在 quotient(ntrans 1) 中，
且不在 `core (rtrans 1)` 中。 -/
theorem nonRDartsTrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) {u : Dart}
    (hu : u ∈ listOfDarts (quotientList L N))
    (hucore : u ∉ listPairs (core L r)) :
    u ∈ listOfDarts (quotientList L (ntrans L N r x 1)) ∧
      u ∉ listPairs (core L (rtrans L N r x 1)) := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hnedg : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  have hN : normalList L hL N := hm.2.1
  have hrN : r ∈ N := hm.2.2.1
  have hm1 : markedList L hL (ntrans L N r x 1) (rtrans L N r x 1) x :=
    Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm 1
  have hN1 : normalList L hL (ntrans L N r x 1) := hm1.2.1
  have hr1 : rtrans L N r x 1 ∈ ntrans L N r x 1 := hm1.2.2.1
  obtain ⟨p, r0, hp, hr0, hd⟩ :=
    (memListOfDartsQuotientChain L hL hN hnedg hunL u).mp hu
  have hne : r0 ≠ r := by
    rintro rfl
    exact hucore (by
      rw [listPairsCoreChain L hL hN hnedg hunL hr0]
      exact List.mem_map.mpr ⟨p, hp, hd.symm⟩)
  constructor
  · have hr0nt : r0 ∈ ntrans L N r x 1 :=
      elementInNtransSuc L hL hgn hm hr0 hne
    exact (memListOfDartsQuotientChain L hL hN1 hnedg hunL u).mpr
      ⟨p, r0, hp, hr0nt, hd⟩
  · intro hmem
    obtain ⟨_, _, _, hpne0, hsub0⟩ :=
      Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN hr0 hp
    have huR0 : u ∈ r0 := by
      rw [hd]
      exact hsub0 _ (getLastBangMem hpne0)
    have huR1 : u ∈ rtrans L N r x 1 :=
      memListPairsCoreImpMemR L hL hN1 hnedg hunL hr1 hmem
    have huR1' : u ∈ (splitNormalList L r (findFaceDarts L (ly L r x))
        (ly L r x) (prevEl r (lz L N r x))).2 := by
      rw [← Kepler.Text.Reduction3.rtrans1 L N r x hnf]
      exact huR1
    have hsplit := split2MemChain L hL hgn hunL hm hnf huR1'
    have huFlat : u ∈ N.flatten := memFlattenOfQuotDart L hL hN hnedg hunL hu
    rcases hsplit with hur | hnot
    · exact hne (Kepler.Text.MoreLemma2Naming.uniqSublistUnique N hN.1 r hrN r0 hr0
        ⟨u, hur, huR0⟩).symm
    · exact hnot huFlat

/-! ## §4 迭代件与 0 实例（HOL `non_r_darts_trans_i` / `list_of_darts_mem`） -/

/-- 状态步复合（定义级）：状态 j 的一步 = 状态 (j+1)（`ntrans` 侧）。 -/
theorem ntransStateComp (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (i : ℕ) :
    ntrans L (ntrans L N r x i) (rtrans L N r x i) x 1 = ntrans L N r x (i + 1) := by
  have hpair : (ntrans L N r x i, rtrans L N r x i)
      = (transformList L x)^[i] (N, r) := by
    rw [Prod.mk.injEq]
    exact ⟨rfl, rfl⟩
  show ((transformList L x)^[1] (ntrans L N r x i, rtrans L N r x i)).1
      = ((transformList L x)^[i + 1] (N, r)).1
  rw [hpair, Function.iterate_succ_apply' (transformList L x) i (N, r),
    Function.iterate_one]

/-- **HOL `non_r_darts_trans_i`**（reduction4.hl:3530）：`non_r_darts_trans` 的
`i ≤ transform_count` 迭代形。 -/
theorem nonRDartsTransI (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) {u : Dart} :
    ∀ i, i ≤ transformCount L N r x →
      u ∈ listOfDarts (quotientList L N) →
      u ∉ listPairs (core L r) →
      u ∈ listOfDarts (quotientList L (ntrans L N r x i)) ∧
        u ∉ listPairs (core L (rtrans L N r x i)) := by
  intro i
  induction i with
  | zero =>
    intro _ hu huc
    exact ⟨hu, huc⟩
  | succ j ih =>
    intro hj hu huc
    have hj' : j ≤ transformCount L N r x := by omega
    have hlt : j < transformCount L N r x := by omega
    have hstep := ih hj' hu huc
    have hnfj : ¬ finalList L (rtrans L N r x j) :=
      Kepler.Text.Reduction4.transformCount_not j hlt
    have hmj : markedList L hL (ntrans L N r x j) (rtrans L N r x j) x :=
      Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm j
    have hs := nonRDartsTrans L hL hgn hres hmj hnfj hstep.1 hstep.2
    refine ⟨?_, ?_⟩
    · rw [← ntransStateComp]
      exact hs.1
    · rw [← Kepler.Text.TameSpine.rtransStateComp]
      exact hs.2

/-- **HOL `list_of_darts_mem`**（reduction4.hl:3563）：0 实例。
`pair₀ ∉ core r` ∧ `(betwn₀ = [] ⇒ ¬nextEl)` ∧ `betwn₀ = []` ⇒
`pair₀ ∉ list_of_darts (quotient_list L N)`。 -/
theorem listOfDartsMem (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hcore : ((ytrans L N r x 0).1, (ztrans L N r x 0).1) ∉ listPairs (core L r))
    (hnext : between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
      ¬(nextEl (core L r) (ytrans L N r x 0).1 = (ztrans L N r x 0).1))
    (hbet : between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = []) :
    ((ytrans L N r x 0).1, (ztrans L N r x 0).1) ∉ listOfDarts (quotientList L N) := by
  intro hmem
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hnedg : (hypermapOfList L hL).EdgeNondegenerate := hres.edgeNondegenerate
  have hN : normalList L hL N := hm.2.1
  have hm1 : markedList L hL (ntrans L N r x 1) (rtrans L N r x 1) x :=
    Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm 1
  have hN1 : normalList L hL (ntrans L N r x 1) := hm1.2.1
  have hr1 : rtrans L N r x 1 ∈ ntrans L N r x 1 := hm1.2.2.1
  have hstep := nonRDartsTrans L hL hgn hres hm hnf hmem hcore
  apply hstep.2
  -- 目标：`pair₀ ∈ list_pairs (core L (rtrans 1))`
  have hyR1 : ytrans L N r x 0 ∈ rtrans L N r x 1 :=
    memYRtrans1 L hL hgn hnf hm
  have hrnd : r.Nodup := (List.nodup_flatten.mp hN.1).1 r hm.2.2.1
  have hly : ly L r x ∈ findFaceDarts L x :=
    Kepler.Text.MoreLemma2a23.ytranMeF L hL hm rfl 0
  have hr1nd : (rtrans L N r x 1).Nodup :=
    (List.nodup_flatten.mp hN1.1).1 _ hr1
  have hbet' : between (findFaceDarts L x) (ly L r x) (lz L N r x) = [] := hbet
  have hexp : rtrans L N r x 1
      = [ztrans L N r x 0]
        ++ (between r (ztrans L N r x 0) (ytrans L N r x 0) ++ [ytrans L N r x 0]) := by
    rw [rtrans1Eq L hL hnf hrnd hly]
    simp only [hbet', List.append_nil]
    rfl
  have hry : nextEl (rtrans L N r x 1) (ytrans L N r x 0) = (ztrans L N r x 0) := by
    rw [hexp]
    exact nextElCatLastHead (ztrans L N r x 0) (ytrans L N r x 0)
      (between r (ztrans L N r x 0) (ytrans L N r x 0)) (by rw [← hexp]; exact hr1nd)
  have hne : (ytrans L N r x 0).1 ≠ (ztrans L N r x 0).1 :=
    qrdyxyjFstYNeFstZ L hL hgn hm hnf
  have hcu1 : (core L (rtrans L N r x 1)).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm1
  have hnc := nextCoreNeFST L hL hgn hres hN1 hr1 hyR1 hcu1 hne hry
  have hmemCore : (ytrans L N r x 0).1 ∈ core L (rtrans L N r x 1) :=
    Kepler.Text.Reduction4Idx.memFstCore L hL hm1 hyR1
  exact memListPairsCoreOfNextEl L hL hgn hunL hnedg hN1 hr1 hcu1 hmemCore hnc

/-! ## §5 `k3Sx3Slot` 消槽（HOL `list_of_darts_reduction` 第三合取，:3694–3708） -/

/-- **SX-c 主交付**：`k3Sx3Slot` 的实例。
`i < k` 且 `betwn f y_i z_i = []` ⇒ `(y_i.1, z_i.1) ∉ list_of_darts (quotient L N)`。 -/
theorem k3Sx3SlotInstance : k3Sx3Slot := by
  intro L hL hgn hres N r x k hm hnf hk i hi hbet hmem
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  -- (0) `core L r` 侧的 0 实例前提（BETWN 3 的 h0）
  have h0 : ∀ (L' : fgraph ℕ) (hL' : GoodList L') (N' : List (List Dart))
      (r' : List Dart) (x' : Dart),
      GoodListNodesTl L' hL' → (hypermapOfList L' hL').IsRestricted →
      markedList L' hL' N' r' x' → ¬ finalList L' r' →
      between (findFaceDarts L' x') (ytrans L' N' r' x' 0) (ztrans L' N' r' x' 0) = [] →
      ¬(nextEl (core L' r') (ytrans L' N' r' x' 0).1 = (ztrans L' N' r' x' 0).1) := by
    intro L' hL' N' r' x' hgn' hres' hm' hnf' hbet'
    have haq' : Kepler.Text.Reduction4Idx.AqiunppSlot L' hL' :=
      fun hgn'' N'' r'' x'' hm'' j =>
        Kepler.Text.TameSpine.aqiunpp L' hL' hgn'' N'' r'' x'' hm'' j
    have huniq' : (core L' r').Nodup :=
      Kepler.Text.Reduction4Idx.markedListUniqCore L' hL' hm'
    have hne0' : transformCount L' N' r' x' ≠ 0 :=
      transformCountNon0OfMarked L' hL' hgn' haq' hm' hnf'
    have hmain' := finalAssumptionsNotNextCore0I L' hL' hgn' hres' haq'
      (transformCount L' N' r' x') hm' hnf' rfl
    exact (betwnCoreReductionLemma L' N' r' x' (transformCount L' N' r' x')
      huniq' hne0' hmain').1 hbet'
  have huniq : (core L r).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hne0 : transformCount L N r x ≠ 0 :=
    transformCountNon0OfMarked L hL hgn haq hm hnf
  have hmain := finalAssumptionsNotNextCore0I L hL hgn hres haq
    (transformCount L N r x) hm hnf rfl
  -- (1) 状态 0：pair_i ∉ list_pairs (core L r)
  have hcore : ((ytrans L N r x i).1, (ztrans L N r x i).1) ∉ listPairs (core L r) :=
    (betwnCoreReductionLemma L N r x (transformCount L N r x) huniq hne0 hmain).2
      i (by omega) hbet
  -- (2) non_r_darts_trans_i：pair_i ∈ quot(ntrans i) ∧ pair_i ∉ core(rtrans i)
  have hi' : i ≤ transformCount L N r x := by omega
  have hsi := nonRDartsTransI L hL hgn hres hm hnf i hi' hmem hcore
  -- (3) 状态 i 的 marked/¬final 与计数
  have hnfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by omega)
  have hmi : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x :=
    Kepler.Text.TameSpine.aqiunpp L hL hgn N r x hm i
  have htc := transformCountAddOfMarked L hL hgn haq hm i hi'
  have hpos : 0 < transformCount L (ntrans L N r x i) (rtrans L N r x i) x := by
    rw [htc]
    omega
  -- (4) 状态 i 的 betwn/nextEl 前件（transAdd 折叠）
  have hta := Kepler.Text.Reduction3.transAdd L N r x i 0
  rw [Nat.zero_add] at hta
  have hbet_i : between (findFaceDarts L x)
      (ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0)
      (ztrans L (ntrans L N r x i) (rtrans L N r x i) x 0) = [] := by
    rw [← hta.2.2.1, ← hta.2.2.2]
    exact hbet
  have hnext_i : between (findFaceDarts L x)
      (ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0)
      (ztrans L (ntrans L N r x i) (rtrans L N r x i) x 0) = [] →
      ¬(nextEl (core L (rtrans L N r x i))
          (ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0).1
        = (ztrans L (ntrans L N r x i) (rtrans L N r x i) x 0).1) := by
    intro hb
    exact finalAssumptionsNotNextCore0I L hL hgn hres haq
      (transformCount L (ntrans L N r x i) (rtrans L N r x i) x) hmi hnfi rfl
      0 hpos hb
  -- (5) 状态 i 的 0 实例
  have hmem0 := listOfDartsMem L hL hgn hres hmi hnfi hsi.2 hnext_i hbet_i
  -- (6) 与 hsi.1 相抵
  have hmem_i : ((ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0).1,
      (ztrans L (ntrans L N r x i) (rtrans L N r x i) x 0).1)
      ∈ listOfDarts (quotientList L (ntrans L N r x i)) := by
    rw [← hta.2.2.1, ← hta.2.2.2]
    exact hsi.1
  exact hmem0 hmem_i

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.listPairsCoreChain
#print axioms Kepler.Text.Reduction5.memListOfDartsQuotientChain
#print axioms Kepler.Text.Reduction5.memListOfDartsQuotientCore
#print axioms Kepler.Text.Reduction5.memFlattenOfQuotDart
#print axioms Kepler.Text.Reduction5.memListPairsCoreImpMemR
#print axioms Kepler.Text.Reduction5.memListPairsCoreOfNextEl
#print axioms Kepler.Text.Reduction5.split2MemChain
#print axioms Kepler.Text.Reduction5.nonRDartsTrans
#print axioms Kepler.Text.Reduction5.ntransStateComp
#print axioms Kepler.Text.Reduction5.nonRDartsTransI
#print axioms Kepler.Text.Reduction5.listOfDartsMem
#print axioms Kepler.Text.Reduction5.k3Sx3SlotInstance

/- 接口探针：`k3Sx3SlotInstance` 可直接替换 ml15 的 `hSx3` 槽。 -/
#check fun (hF8 : Kepler.Text.Reduction5.k3Indexf8Slot)
    (hUvns : Kepler.Text.Reduction5.k3UvnsSlot) =>
  Kepler.Text.Reduction5.reductionK3ConclOfSlots hF8
    Kepler.Text.Reduction5.k3Sx3SlotInstance hUvns
