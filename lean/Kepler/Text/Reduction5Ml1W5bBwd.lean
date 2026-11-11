/-
  Kepler.Text.Reduction5Ml1W5bBwd — W5b 逆向件（`d ∈ r → d ∈ rtrans 1`；HOL more_lemma1.hl:1243–:1468）
  + 链形 `KBWPBHQ2` 包装（树内仅 spine `kbwpbhq2Spine`；按派单先例「链→spine 桥 + spine 消费 + 桥回」）。

  路线（比 HOL 短）：betwn_cases 四分支；唯 `d ∈ betwn r y z` 分支需几何核：
  取 `k = min_num{n | ¬(fList((prevEl r)^(n+1) d) = (prevEl r)^n d)}`、`d1 = (prevEl r)^k d`；
  · `k < indexf w d r` 支：`d1` 是 d 之前最近的断点 ⇒ `d1 ∈ f`（后向归纳）+ KBWPBHQ2
    ⇒ `d1 = ztrans j`；j=0 与 j≥1 都撞 `indexfZtransLt`（W5a）与 `d1` 位于 d 之前；
  · `k ≥ indexf w d r` 支：w→d 的 r 弧全为 f 步 ⇒ `indexf w d f = indexf w d r` 且
    z 在 f 上位于 d 之前（因其 r 位置在 d 之后），与 hle 相抵。
  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction5Ml1W5bFwd
import Kepler.Text.TameSpine.Reduction3Kbwpbhq2
import Kepler.Text.TameSpine.Reduction3ChainFinalBridge
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.TameSpine.JcajyduAqSplit1C
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction5J5Tav2Bridge
import Kepler.Text.PwssratEngine
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList eList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList findList)

/-! ## §1 链形 `KBWPBHQ2`（spine 消费 + 桥回） -/

/-- 任意 `i < transformCount` 处 `ztrans` 的链↔spine 等式。 -/
theorem ztransEqSpineAt (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) {i : ℕ} (hi : i < transformCount L N r x) :
    ztrans L N r x i = Kepler.Text.TameSpine.ztransSpine L N r x i := by
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hf : ¬ finalList L (rtrans L N r x i) := Kepler.Text.Reduction4.transformCount_not i hi
  have hnt := Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm i
  have hrt := Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i
  have hmAt : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x := haq hgn N r x hm i
  have hlz := Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hmAt hf
  show lz L (ntrans L N r x i) (rtrans L N r x i) x
    = Kepler.Text.TameSpine.lZSpine L (Kepler.Text.TameSpine.ntransSpine L N r x i)
        (Kepler.Text.TameSpine.rtransSpine L N r x i) x
  rw [hlz, hnt, hrt]

/-- **HOL `Kbwpbhq.KBWPBHQ2`**（KBWPBHQ.hl:1794）链形：
`u ∈ r ∧ u ∈ f ⇒ ((∃i, ztrans i = u ∧ i < transformCount) ⟺ ¬(fList(prevEl(findList N u) u) = u))`。 -/
theorem kbwpbhq2Chain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x)
    {u : Dart} (hur : u ∈ r) (huf : u ∈ findFaceDarts L x) :
    (∃ i, ztrans L N r x i = u ∧ i < transformCount L N r x)
      ↔ ¬ (fList L (prevEl (findList N u) u) = u) := by
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hfind : findList N u = r := by
    rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
    exact Kepler.Text.TameSpine.findListUniq hm.2.1.1 hur hm.2.2.1
  rw [hfind]
  by_cases hf : finalList L r
  · -- final：transformCount = 0；两侧皆假
    have hmem0 : (0 : ℕ) ∈ {i : ℕ | finalList L (rtrans L N r x i)} := by
      simpa [Kepler.Text.Reduction5.rtrans_zero] using hf
    have hne : ({i : ℕ | finalList L (rtrans L N r x i)} : Set ℕ).Nonempty := ⟨0, hmem0⟩
    have hle0 : transformCount L N r x ≤ 0 := by
      have h := (Kepler.Text.Reduction5.minNum_spec hne).2 0 hmem0
      unfold transformCount
      exact h
    have htc : transformCount L N r x = 0 := by omega
    have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
    have hprev : prevEl r u ∈ r := Kepler.Text.Reduction5.memPrevEl hur
    have h1 : fList L (prevEl r u) = nextEl r (prevEl r u) := hf _ hprev
    have h2 : @nextEl Dart instBEqProd r (prevEl r u) = u := by
      rw [Kepler.Text.Reduction5.nextElInstEq]
      exact Kepler.Text.Reduction5.nextPrevId hrnd u
    have hfu : fList L (prevEl r u) = u := by rw [h1, h2]
    constructor
    · rintro ⟨i, -, hi⟩; omega
    · intro hcon; exact absurd hfu hcon
  · -- 非 final：spine 消费 + 桥回
    have htc : transformCount L N r x = Kepler.Text.TameSpine.transformCountSpine L N r x :=
      Kepler.Text.TameSpine.transformCountEqSpineOfAq L hL hgn haq hm hf
    have hta : Kepler.Text.TameSpine.transformAssumptionSpine L hL :=
      Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq
    have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hf
    have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
      (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm
    constructor
    · rintro ⟨i, hzi, hi⟩
      have hziS : Kepler.Text.TameSpine.ztransSpine L N r x i = u := by
        rw [← ztransEqSpineAt L hL hgn haq hm hi]
        exact hzi
      have hiS : i < Kepler.Text.TameSpine.transformCountSpine L N r x := by omega
      have h := (Kepler.Text.TameSpine.kbwpbhq2Spine L hL hta hgn hunL hmS hur huf).mp
        ⟨i, hziS, hiS⟩
      have h' : ¬ (fList L (prevEl (findList N u) u) = u) := by
        rwa [← Kepler.Text.ChainBridge.findList_eq_findListSpine] at h
      rwa [hfind] at h'
    · intro hcon
      have hcon' : ¬ (fList L (prevEl (findList N u) u) = u) := by
        rwa [hfind]
      have hconS : ¬ (fList L (prevEl (Kepler.Text.TameSpine.findListSpine N u) u) = u) := by
        rwa [← Kepler.Text.ChainBridge.findList_eq_findListSpine]
      obtain ⟨i, hziS, hiS⟩ :=
        (Kepler.Text.TameSpine.kbwpbhq2Spine L hL hta hgn hunL hmS hur huf).mpr hconS
      refine ⟨i, ?_, ?_⟩
      · rw [ztransEqSpineAt L hL hgn haq hm (by omega)]
        exact hziS
      · omega


/-! ## §2 逆向几何核（HOL more_lemma1.hl:1243–:1468 的短路线重排） -/

/-- 后向 `prevEl` 幂与前向 `nextEl` 幂在 `r` 上的互补：`d = (nextEl)^D w` 时
`(prevEl)^k d = (nextEl)^(D-k) w`（`k ≤ D`）。 -/
private theorem prevPowEqNextPowSub {r : List Dart} (hrnd : r.Nodup) {w d : Dart}
    (hw : w ∈ r) {D : ℕ} (hD : (nextEl r)^[D] w = d) :
    ∀ k ≤ D, (prevEl r)^[k] d = (nextEl r)^[D - k] w := by
  intro k
  induction k with
  | zero => intro _; simpa using hD.symm
  | succ q ih =>
    intro hq
    have hq' : q ≤ D := by omega
    have hstep : (prevEl r)^[q + 1] d = prevEl r ((prevEl r)^[q] d) :=
      Function.iterate_succ_apply' (prevEl r) q d
    rw [hstep, ih hq']
    have hsplit : D - q = (D - q - 1) + 1 := by omega
    rw [hsplit, Function.iterate_succ_apply']
    have hmem : (nextEl r)^[D - q - 1] w ∈ r := by
      induction (D - q - 1) with
      | zero => simpa using hw
      | succ m ihm =>
        rw [Function.iterate_succ_apply']
        exact Kepler.Text.TameLp.nextEl_mem_of_mem ihm
    exact Kepler.Text.TameLp.prevEl_nextEl hrnd hmem

/-- 断点集非空（witness `n = indexf (l'z) d r`；用 spine `prevRNotEqF` 的链桥）。 -/
private theorem w5bBreakMem (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {d : Dart} (hdr : d ∈ r) :
    ¬ (fList L ((prevEl r)^[Kepler.Text.Reduction5.indexf (lz L N r x) d r + 1] d)
      = (prevEl r)^[Kepler.Text.Reduction5.indexf (lz L N r x) d r] d) := by
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  obtain ⟨-, hzr0, -, -, -, -, -, -, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hzr : lz L N r x ∈ r := by
    simpa [Kepler.Text.Reduction5.ztrans_def, Kepler.Text.Reduction5.ntrans_zero,
      Kepler.Text.Reduction5.rtrans_zero] using hzr0
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  -- 后向幂 = l'z
  have h1 : (@nextEl Dart instBEqOfDecidableEq r)^[Kepler.Text.Reduction5.indexf
      (lz L N r x) d r] (lz L N r x) = d :=
    Kepler.Text.MoreLemma2Island1.indexfN hzr hdr hrnd
  have h2 : (@nextEl Dart instBEqProd r)^[Kepler.Text.Reduction5.indexf
      (lz L N r x) d r] (lz L N r x) = d := by
    rw [Kepler.Text.Reduction5.iterateInstEq]
    exact h1
  have h3 : (prevEl r)^[Kepler.Text.Reduction5.indexf (lz L N r x) d r] d
      = lz L N r x :=
    (Kepler.Text.Reduction4Idx.symPowerPrevNext hrnd hdr hzr _).mpr h2
  -- fList(prev_el z) ≠ z（spine 桥）
  have hprevNE : fList L (prevEl r (lz L N r x)) ≠ lz L N r x := by
    have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hnf
    have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
      (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm
    have hfS : ¬ Kepler.Text.TameSpine.finalListSpine L r :=
      fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)
    have h := Kepler.Text.TameSpine.prevRNotEqF L hL hgn hunL hmS hfS
    have hlz := Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf
    rwa [← hlz] at h
  rw [Function.iterate_succ_apply', h3]
  exact hprevNE

/-! ## §3 后向 f 成员归纳、f-弧行走、逆向主件 -/

/-- 窗内索引算术（PBFLHET.hl:166–209 证体尾墙的链孪生；
树内同体私件 `TameSpine.indexfBetweenArith` 跨模块不可见，故同体重落）：
`w,y,z,d ∈ s ∧ y≠z ∧ d ∈ betwn s y z ∧ indexf w y s < indexf w z s ⇒
indexf w d s < indexf w z s ∧ indexf w y s < indexf w d s`。 -/
private theorem w5bIndexfBetweenArith {s : List Dart} {w y z d : Dart}
    (hsnd : s.Nodup) (hws : w ∈ s) (hys : y ∈ s) (hzs : z ∈ s)
    (hne : y ≠ z) (hbet : d ∈ @Kepler.Graphs.between Dart instBEqProd s y z)
    (hlt : indexf w y s < indexf w z s) :
    indexf w d s < indexf w z s ∧ indexf w y s < indexf w d s := by
  have hbetD : d ∈ @Kepler.Graphs.between Dart instBEqOfDecidableEq s y z := by
    rwa [Kepler.Text.Reduction5.betweenInstEq s y z] at hbet
  obtain ⟨hp1, hp2⟩ :=
    (Kepler.Text.Reduction5.indexfBetwnEq hne hsnd hys hzs).mp hbetD
  have hds : d ∈ s := Kepler.Text.Reduction5.betwnMem hbetD
  have hA := Kepler.Text.Reduction4.indexf_add_left hws hys hzs (Nat.le_of_lt hlt)
  have hB := Kepler.Text.Reduction4.indexf_add_left hys hds hzs (le_of_lt hp2)
  have hC := Kepler.Text.Reduction4.indexf_add_right hws hds hzs (by omega)
  omega

/-- 后向 `k` 步内保持 `f`：断点前每步都是 f 步，f 步的逆仍是 f 成员。 -/
private theorem w5bBackMemF (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x)
    {d : Dart} (hdr : d ∈ r) (hdf : d ∈ findFaceDarts L x)
    {k : ℕ} (heq : ∀ n < k, fList L ((prevEl r)^[n + 1] d) = (prevEl r)^[n] d) :
    ∀ i ≤ k, (prevEl r)^[i] d ∈ findFaceDarts L x := by
  intro i
  induction i with
  | zero => intro _; simpa using hdf
  | succ q ih =>
    intro hq
    have hq' : q ≤ k := by omega
    have hpq := ih hq'
    have hstep : fList L ((prevEl r)^[q + 1] d) = (prevEl r)^[q] d := heq q (by omega)
    have hmemR : (prevEl r)^[q + 1] d ∈ r :=
      Kepler.Text.Reduction4Idx.memPrevPower hdr (q + 1)
    have hmemD : (prevEl r)^[q + 1] d ∈ listOfDarts L :=
      ((hm.2.1.2.2.2.1 r hm.2.2.1) _ hmemR).1
    have hinv := Kepler.Text.TameLp.prev_fList_inverse hL.1 hmemD
    rw [hstep] at hinv
    have hcongr : findFaceDarts L ((prevEl r)^[q] d) = findFaceDarts L x :=
      Kepler.Text.Reduction5.memFindFaceImpFacesEq hL.1 hpq
    rw [hcongr] at hinv
    rw [← hinv]
    exact Kepler.Text.TameLp.prevEl_mem_of_mem hpq

/-- 无断点时 `w → d` 的 r 弧与 f 弧逐步重合。 -/
private theorem w5bWalkAgree (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hrnd : r.Nodup)
    {w d : Dart} (hwr : w ∈ r) (hwf : w ∈ findFaceDarts L x)
    (hxd : x ∈ listOfDarts L)
    {D : ℕ} (hD : (nextEl r)^[D] w = d)
    {k : ℕ} (heq : ∀ n < k, fList L ((prevEl r)^[n + 1] d) = (prevEl r)^[n] d)
    (hkD : D ≤ k) :
    ∀ p ≤ D, (nextEl r)^[p] w = (nextEl (findFaceDarts L x))^[p] w := by
  have hufAll : ∀ m, (nextEl (findFaceDarts L x))^[m] w ∈ findFaceDarts L x := by
    intro m
    induction m with
    | zero => simpa using hwf
    | succ j ihj =>
      rw [Function.iterate_succ_apply']
      exact Kepler.Text.TameLp.nextEl_mem_of_mem ihj
  intro p
  induction p with
  | zero => intro _; rfl
  | succ q ih =>
    intro hqD
    have hq : q ≤ D := by omega
    have hn : D - q - 1 < k := by omega
    have heqn : fList L ((prevEl r)^[D - q - 1 + 1] d) = (prevEl r)^[D - q - 1] d :=
      heq _ hn
    have hpq : (prevEl r)^[D - q - 1 + 1] d = (nextEl r)^[q] w := by
      have h := prevPowEqNextPowSub hrnd hwr hD (D - q - 1 + 1) (by omega)
      simpa [show D - (D - q - 1 + 1) = q from by omega] using h
    have hpq1 : (prevEl r)^[D - q - 1] d = (nextEl r)^[q + 1] w := by
      have h := prevPowEqNextPowSub hrnd hwr hD (D - q - 1) (by omega)
      simpa [show D - (D - q - 1) = q + 1 from by omega] using h
    have hstep : (nextEl r)^[q + 1] w = fList L ((nextEl r)^[q] w) := by
      rw [← hpq1, ← hpq]
      exact heqn.symm
    rw [hstep, ih hq]
    have huf : (nextEl (findFaceDarts L x))^[q] w ∈ findFaceDarts L x := hufAll q
    have hfindU : findFaceDarts L ((nextEl (findFaceDarts L x))^[q] w)
        = findFaceDarts L x :=
      Kepler.Text.TameLp.findFaceDarts_congr_of_mem hL.1 hxd huf
    rw [Function.iterate_succ_apply']
    show fList L ((nextEl (findFaceDarts L x))^[q] w)
      = nextEl (findFaceDarts L x) ((nextEl (findFaceDarts L x))^[q] w)
    simp only [fList]
    rw [hfindU]

/-- **W5b 逆向（HOL more_lemma1.hl:1243–:1468 的结论）**：
`d ∈ f` 且 `indexf w z f ≤ indexf w d f` ⇒ `d ∈ r → d ∈ rtr 1`。 -/
theorem rRtransEqBwd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {d : Dart} (hd : d ∈ findFaceDarts L x)
    (hle : indexf (nextEl (findFaceDarts L x) x) (lz L N r x) (findFaceDarts L x)
      ≤ indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x)) :
    d ∈ r → d ∈ rtrans L N r x 1 := by
  intro hdr
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hxd : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  obtain ⟨hlyf, hzf, hltf⟩ := Kepler.Text.Reduction4Idx.pplhuljV0 L hL hgn hunL hm hnf
  obtain ⟨hlyr, hzr0, -, -, -, -, -, -, -⟩ := ml1SetupMem L hL hgn hm hnf
  have hzr : lz L N r x ∈ r := by
    simpa [Kepler.Text.Reduction5.ztrans_def, Kepler.Text.Reduction5.ntrans_zero,
      Kepler.Text.Reduction5.rtrans_zero] using hzr0
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hfnd : (findFaceDarts L x).Nodup := Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hxr : x ∈ r := hm.2.2.2.1
  set w : Dart := nextEl (findFaceDarts L x) x with hwdef
  have hwr : w ∈ r := by
    rw [hwdef]
    show fList L x ∈ r
    rw [← hm.2.2.2.2.2.1]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr
  have hwf : w ∈ findFaceDarts L x := by
    rw [hwdef]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem
      ((Kepler.Text.TameLp.dart_in_face L x).mpr hxd)
  have hle' : indexf w (lz L N r x) (findFaceDarts L x)
      ≤ indexf w d (findFaceDarts L x) := by
    rw [hwdef]
    exact hle
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i
  have hne : ly L r x ≠ lz L N r x := by
    intro e
    rw [e] at hltf
    exact absurd hltf (lt_irrefl _)
  have hrt := rtrans1Eq (N := N) (r := r) (x := x) L hL hnf hrnd hlyf
  rw [hrt]
  rcases Kepler.Text.TameSpine.betwnCases (s := r) (x := ly L r x) (y := d)
    (z := lz L N r x) hne hrnd hlyr hdr hzr with hdy | hdz | hdb | hdb
  · rw [hdy]; simp
  · rw [hdz]; simp
  · -- 硬支：d ∈ betwn r y z
    have hPK : indexf w (ly L r x) r < indexf w (lz L N r x) r := by
      rw [hwdef]
      exact Kepler.Text.Reduction4Idx.indexfYLeZInR0 L hL hgn hunL hm hnf
    have hord := w5bIndexfBetweenArith hrnd hwr hlyr hzr hne hdb hPK
    set D : ℕ := indexf w d r with hDdef
    set K : ℕ := indexf w (lz L N r x) r with hKdef
    have hDK : D < K := hord.1
    have hSne : ({n : ℕ | ¬ (fList L ((prevEl r)^[n + 1] d)
        = (prevEl r)^[n] d)}).Nonempty := ⟨_, w5bBreakMem L hL hgn hm hnf hdr⟩
    set k : ℕ := Kepler.Text.Reduction5.minNum
      {n : ℕ | ¬ (fList L ((prevEl r)^[n + 1] d) = (prevEl r)^[n] d)} with hkdef
    have hspec : k ∈ {n : ℕ | ¬ (fList L ((prevEl r)^[n + 1] d)
        = (prevEl r)^[n] d)} ∧
        ∀ n ∈ {n : ℕ | ¬ (fList L ((prevEl r)^[n + 1] d)
          = (prevEl r)^[n] d)}, k ≤ n := by
      rw [hkdef]
      exact Kepler.Text.Reduction5.minNum_spec hSne
    have hkmem : fList L ((prevEl r)^[k + 1] d) ≠ (prevEl r)^[k] d := hspec.1
    have hkle : k ≤ Kepler.Text.Reduction5.indexf (lz L N r x) d r :=
      hspec.2 _ (w5bBreakMem L hL hgn hm hnf hdr)
    have heq : ∀ n < k, fList L ((prevEl r)^[n + 1] d) = (prevEl r)^[n] d := by
      intro n hn
      exact not_not.mp (Kepler.Text.Reduction4Idx.minnumNot hkdef.symm hn)
    set d1 : Dart := (prevEl r)^[k] d with hd1def
    have hd1r : d1 ∈ r := Kepler.Text.Reduction4Idx.memPrevPower hdr k
    have hDpowD : (@nextEl Dart instBEqOfDecidableEq r)^[D] w = d := by
      rw [hDdef]
      exact Kepler.Text.MoreLemma2Island1.indexfN hwr hdr hrnd
    have hDpow : (nextEl r)^[D] w = d := by
      rw [Kepler.Text.Reduction5.iterateInstEq]
      exact hDpowD
    by_cases hkD : k < D
    · -- 最近断点在 d 之前
      have hsub := prevPowEqNextPowSub hrnd hwr hDpow k (le_of_lt hkD)
      have hd1eq : d1 = (nextEl r)^[D - k] w := by
        rw [hd1def]
        exact hsub
      have hDklt : D - k < r.length := by
        have hlt := Kepler.Text.Reduction4.indexf_lt_length_of_mem hwr hdr
        rw [← hDdef] at hlt
        omega
      have hpowD : (@nextEl Dart instBEqOfDecidableEq r)^[D - k] w = d1 := by
        rw [← Kepler.Text.Reduction5.iterateInstEq]
        exact hd1eq.symm
      have hd1idx : indexf w d1 r = D - k :=
        Kepler.Text.MoreLemma2Island1.nextElnIndexf hwr hd1r hrnd hpowD hDklt
      have hd1f : d1 ∈ findFaceDarts L x :=
        w5bBackMemF L hL hm hdr hd heq k le_rfl
      have hkmem' : fList L (prevEl r d1) ≠ d1 := by
        have hstep : (prevEl r)^[k + 1] d = prevEl r d1 := by
          rw [Function.iterate_succ_apply', hd1def]
        have h2 := hkmem
        rw [hstep] at h2
        exact h2
      have hfindd1 : findList N d1 = r := by
        rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
        exact Kepler.Text.TameSpine.findListUniq hm.2.1.1 hd1r hm.2.2.1
      have hcon : ¬ (fList L (prevEl (findList N d1) d1) = d1) := by
        rw [hfindd1]
        exact hkmem'
      obtain ⟨j, hzj, hjtc⟩ :=
        (kbwpbhq2Chain L hL hgn haq hm hd1r hd1f).mpr hcon
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · have hd1z : d1 = lz L N r x := by
          rw [← hzj, hj0]
          rfl
        have hidxK : indexf w d1 r = K := by
          rw [hd1z, hKdef]
        exact absurd hidxK (by omega)
      · have hzlt := Kepler.Text.Reduction5.indexfZtransLt L hL hgn hm hnf
          (f := findFaceDarts L x) (w := w) rfl hwdef.symm j hjpos hjtc
        have hKlt : K < indexf w d1 r := by
          rw [hKdef, ← hzj]
          exact hzlt
        exact absurd hKlt (by omega)
    · -- 无断点：w→d 全为 f 步
      have hkD' : D ≤ k := by omega
      have hwalk := w5bWalkAgree L hL hm hrnd hwr hwf hxd hDpow heq hkD'
      have hdw : d = (nextEl (findFaceDarts L x))^[D] w := by
        rw [← hDpow]
        exact hwalk D le_rfl
      set iz : ℕ := indexf w (lz L N r x) (findFaceDarts L x) with hizdef
      have hleiz : iz ≤ indexf w d (findFaceDarts L x) := hle'
      by_cases hizD : iz ≤ D
      · have hzwalk : (nextEl (findFaceDarts L x))^[iz] w = (nextEl r)^[iz] w :=
          (hwalk iz hizD).symm
        have hzfpow : (@nextEl Dart instBEqOfDecidableEq (findFaceDarts L x))^[iz] w
            = lz L N r x := by
          rw [hizdef]
          exact Kepler.Text.MoreLemma2Island1.indexfN hwf hzf hfnd
        have hzfpowP : (nextEl (findFaceDarts L x))^[iz] w = lz L N r x := by
          rw [Kepler.Text.Reduction5.iterateInstEq]
          exact hzfpow
        have hzrpowD : (@nextEl Dart instBEqOfDecidableEq r)^[iz] w = lz L N r x := by
          rw [← Kepler.Text.Reduction5.iterateInstEq, ← hzwalk]
          exact hzfpowP
        have hizr : iz < r.length := by
          have hlt := Kepler.Text.Reduction4.indexf_lt_length_of_mem hwr hdr
          rw [← hDdef] at hlt
          omega
        have hKiz : K = iz := by
          rw [hKdef]
          exact Kepler.Text.MoreLemma2Island1.nextElnIndexf hwr hzr hrnd hzrpowD hizr
        exact absurd hKiz (by omega)
      · -- z 在 d 之后
        have hDiz : D < iz := by omega
        have hDflt : D < (findFaceDarts L x).length := by
          have hlt := Kepler.Text.Reduction4.indexf_lt_length_of_mem hwf hzf
          rw [← hizdef] at hlt
          omega
        have hdpowD : (@nextEl Dart instBEqOfDecidableEq (findFaceDarts L x))^[D] w
            = d := by
          rw [← Kepler.Text.Reduction5.iterateInstEq]
          exact hdw.symm
        have hdfidx : indexf w d (findFaceDarts L x) = D :=
          Kepler.Text.MoreLemma2Island1.nextElnIndexf hwf hd hfnd hdpowD hDflt
        exact absurd hleiz (by omega)
  · simp [hdb]

/-- **W5b 主件（HOL `r_rtrans_eq_thm`，more_lemma1.hl:1162–:1527）**：
`good_list ∧ good_list_nodes ∧ marked_list ∧ ¬final_list ⇒ r_rtrans_eq`。
落库后可消 `nfgtransFst`/`mainInduction` 的 `hrreAll` 前提（台账联动）。 -/
theorem rRtransEqThm (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    rRtransEq L N r x := by
  unfold rRtransEq
  dsimp only
  intro d hd hle
  exact ⟨fun h => rRtransEqBwd L hL hgn hm hnf hd hle h,
    fun h => rRtransEqFwd L hL hgn hm hnf hd hle h⟩

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.ztransEqSpineAt
#print axioms Kepler.Text.Reduction5.kbwpbhq2Chain
#print axioms Kepler.Text.Reduction5.prevPowEqNextPowSub
#print axioms Kepler.Text.Reduction5.w5bBreakMem
#print axioms Kepler.Text.Reduction5.rRtransEqBwd
#print axioms Kepler.Text.Reduction5.rRtransEqThm

