/-
  Kepler.Text.Reduction5Ml1W3a — 主机 8b W3a：f2 半（对称）setup 与 LAST 归属
  （HOL more_lemma1.hl:2644–:2850）。

  ┌─ 件目与 HOL 锚 ────────────────────────────────────────────────
  │ `ml1BracketUniq`（泛用括号段 Nodup；B2 的 u/v 泛化形） | more_lemma1:2226 同型 |
  │ `ml1S2` def（f2 半列表 `[z] ++ (betwn r z y ++ [y])`） | :2675 `s=cat [z] (cat (betwn r z y) [y])` |
  │ `ml1S2Mem` / `ml1S2Last` / `ml1S2Head` | :2676/:2686 + `last_cat`/`hd_cat` |
  │ `ml1S2Uniq` | :2696 `uniq_snd_split_norm` 的 `Seq.cat_uniq` 支 |
  │ `ml1PartEnd2`（f2 LAST 侧内核） | :2760–:2792 |
  │ `ml1Pz1Last`（f2 的 `LAST pz1 = LAST pz`） | :2760 |
  │ `ml1S2LastNe`（f2 端点严格性 + next_el 归约） | :2769–:2792 |
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（DIFFERS）────────────────────────────────────────────────
  │ f2 与 f1 对称：`s2 = [z] ++ (betwn r z y ++ [y])`（`split.2 = s2 ++ betwn f y z`，
  │ s2 是 split.2 的**前缀** ⇒ next_el 归约用 `nextElCat1`；f1 用 `nextElCat2`）。
  │ `ml1PartEnd2` 由 W2b `ml1PartEnd` 逐句镜像：hdfst 的对端是 `y`（不是 `z1`），
  │ s 换 s2、split.1 换 split.2、nextElCat2 换 nextElCat1；其余（state-1
  │ normal_condition 两发、nextCatBetwnSame、块首 FST 单射）同构。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5Ml1W2bQ
import Kepler.Text.Reduction5Ml1W2bU
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList eList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-! ## §0 括号段泛用件 -/

/-- **括号段 Nodup**（B2 `ml1SUniq` 的 u/v 泛化形）：
`u,v ∈ r`、`r.Nodup`、`u ≠ v` ⇒ `[u] ++ (betwn r u v ++ [v])` 无重。
证与 B2 同：`betwnTakeDrop` 两分支 + `getElem_drop'`/`getElem_congr_idx` 端点等式；
wrap 支长度 `r.length - i + j + 1`。 -/
theorem ml1BracketUniq (L : fgraph ℕ) {r : List Dart} {u v : Dart}
    (hnd : r.Nodup) (hu : u ∈ r) (hv : v ∈ r) (huv : u ≠ v) :
    ([u] ++ (between r u v ++ [v])).Nodup := by
  set i := r.idxOf u with hi
  set j := r.idxOf v with hj
  have hiL : i < r.length := List.idxOf_lt_length_iff.mpr hu
  have hjL : j < r.length := List.idxOf_lt_length_iff.mpr hv
  have hgi : r[i]'hiL = u := Kepler.Text.TameLp.getElem_idxOf hu
  have hgj : r[j]'hjL = v := Kepler.Text.TameLp.getElem_idxOf hv
  rw [Kepler.Text.TameSpine.betwnTakeDrop hnd hv, ← hi, ← hj]
  by_cases hlt : i < j
  · rw [if_pos hlt]
    have htake : (r.drop (i + 1)).take (j - i) =
        (r.drop (i + 1)).take (j - i - 1) ++ [v] := by
      conv_lhs => rw [show j - i = (j - i - 1) + 1 from by omega]
      rw [← List.take_append_getElem (by rw [List.length_drop]; omega)]
      congr 1
      rw [List.singleton_inj]
      rw [← List.getElem_drop' (xs := r) (i := i + 1) (j := j - i - 1) (h := by omega),
        getElem_congr_idx (show i + 1 + (j - i - 1) = j by omega), hgj]
    have hEq : [u] ++
        (((r.drop (i + 1)).take (j - (i + 1))) ++ [v])
        = (r.drop i).take (j - i + 1) := by
      rw [show j - (i + 1) = j - i - 1 from by omega, ← htake]
      have hdi : r.drop i = u :: r.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hiL]
        exact congrArg (fun a => a :: r.drop (i + 1)) hgi
      rw [hdi, show j - i + 1 = (j - i) + 1 from by omega, List.take_succ_cons,
        List.singleton_append]
    rw [hEq]
    exact Kepler.Text.TameSpine.uniqTake (Kepler.Text.TameSpine.uniqDrop hnd)
  · rw [if_neg hlt]
    have hji : j < i := by
      have h1 : j ≤ i := by omega
      rcases Nat.lt_or_eq_of_le h1 with h | h
      · exact h
      · exfalso
        apply huv
        exact (List.idxOf_inj hu).mp (by rw [← hi, ← hj]; exact h.symm)
    have htake : r.take (j + 1) = r.take j ++ [v] := by
      rw [← List.take_append_getElem hjL, hgj]
    have hdrop : r.drop i = u :: r.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hiL]
      exact congrArg (fun a => a :: r.drop (i + 1)) hgi
    have hLHS : [u] ++
        (((r.drop (i + 1)) ++ r.take j) ++ [v])
        = (r.drop i) ++ r.take (j + 1) := by
      rw [List.singleton_append, List.append_assoc, ← List.cons_append, ← htake, ← hdrop]
    have hRHS : (r.rotate i).take (r.length - i + j + 1) = (r.drop i) ++ r.take (j + 1) := by
      rw [List.rotate_eq_drop_append_take (by omega : i ≤ r.length), List.take_append,
        List.take_of_length_le (by rw [List.length_drop]; omega),
        show r.length - i + j + 1 - (r.drop i).length = j + 1 from by
          rw [List.length_drop]; omega,
        List.take_take, Nat.min_eq_left (by omega : j + 1 ≤ i)]
    have hEq : [u] ++
        (((r.drop (i + 1)) ++ r.take j) ++ [v])
        = (r.rotate i).take (r.length - i + j + 1) := by
      rw [hLHS, hRHS]
    rw [hEq]
    exact Kepler.Text.TameSpine.uniqTake (List.nodup_rotate.mpr hnd)

/-! ## §1 f2 半列表 `s2` -/

/-- HOL :2675 的 f2 半列表：`s = cat [z] (cat (betwn r z y) [y])`
（`z = ztrans 0 = l'z`、`y = l'y`）。 -/
noncomputable def ml1S2 (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) : List Dart :=
  [ztrans L N r x 0] ++
    (between r (ztrans L N r x 0) (ly L r x) ++ [ly L r x])

/-- f2 半列表的两端成员：`z ∈ s2 ∧ y ∈ s2`（HOL :2676/:2686）。 -/
theorem ml1S2Mem (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) :
    ztrans L N r x 0 ∈ ml1S2 L N r x ∧ ly L r x ∈ ml1S2 L N r x := by
  unfold ml1S2
  constructor <;> simp

/-- f2 半列表末元 = `y`（HOL `last_cat` 两发）。 -/
theorem ml1S2Last (L : fgraph ℕ) {N : List (List Dart)} {r : List Dart} {x : Dart} :
    (ml1S2 L N r x).getLast! = ly L r x := by
  unfold ml1S2
  rw [Kepler.Text.TameSpine.lastCat (u := [ztrans L N r x 0]) (v := _) (by simp),
    Kepler.Text.TameSpine.lastCat (u := _) (v := [ly L r x]) (by simp)]
  simp

/-- f2 半列表首元 = `z`（HOL `hd_cat`，rfl 级）。 -/
theorem ml1S2Head (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) :
    (ml1S2 L N r x).head! = ztrans L N r x 0 := by
  unfold ml1S2
  rfl

/-- f2 半列表 Nodup（`ml1BracketUniq` 于 `u := z`、`v := y`）。 -/
theorem ml1S2Uniq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r) :
    (ml1S2 L N r x).Nodup := by
  obtain ⟨hyr, hzr, -, -, -, -, -, -, hzy⟩ := ml1SetupMem L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  exact ml1BracketUniq L hrnd hzr hyr hzy

/-- `s2` 的成员回落到 `r`（f2 三段：z / between / y）。 -/
theorem ml1S2MemImpR (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {a : Dart} (ha : a ∈ ml1S2 L N r x) : a ∈ r := by
  obtain ⟨hyr, hzr, -, -, -, -, -, -, -⟩ := ml1SetupMem L hL hgn hm hnf
  have ha' : a ∈ [ztrans L N r x 0] ++
      (between r (ztrans L N r x 0) (ly L r x) ++ [ly L r x]) := ha
  rcases List.mem_append.mp ha' with h | h
  · rw [List.mem_singleton] at h
    subst h
    exact hzr
  · rcases List.mem_append.mp h with h | h
    · rw [Kepler.Text.Reduction5.betweenInstEq] at h
      exact Kepler.Text.Reduction5.betwnMem h
    · rw [List.mem_singleton] at h
      subst h
      exact hyr

/-! ## §2 f2 LAST 侧内核与 `LAST pz1 = LAST pz` -/

/-- **W3a 内核（f2 LAST 侧）**：`d ∈ p ∩ p1`（`d.1 ≠ y.1`），
`p ∈ parts L r`，`p1 ∈ parts L s2` 且 `p1 ∈ parts L split.2`，则 `p1.getLast! = p.getLast!`。
（W2b `ml1PartEnd` 的镜像：s → s2、split.1 → split.2、nextElCat2 → nextElCat1、
对端 z1 → y。） -/
theorem ml1PartEnd2 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {p p1 : List Dart} (hp : p ∈ parts L r)
    (hp1 : p1 ∈ parts L (ml1S2 L N r x))
    (hp1s2 : p1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).2)
    {d : Dart} (hd : d ∈ p) (hd1 : d ∈ p1)
    (hdfst : d.1 ≠ (ly L r x).1) :
    p1.getLast! = p.getLast! := by
  obtain ⟨hyr, hzr, -, -, hyf, -, -, -, hzy⟩ := ml1SetupMem L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hzs : ztrans L N r x 0 ∈ ml1S2 L N r x := (ml1S2Mem L N r x).1
  have hsne : ml1S2 L N r x ≠ [] := List.ne_nil_of_mem hzs
  have hds : d ∈ ml1S2 L N r x := ml1PartsMemImp L hsnd hsne hp1 d hd1
  have hp1ne : p1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ p1 hp1
  have hlastmem : p1.getLast! ∈ p1 := Kepler.Text.TameSpine.aqs_getLastMem hp1ne
  have hlasts : p1.getLast! ∈ ml1S2 L N r x :=
    ml1PartsMemImp L hsnd hsne hp1 _ hlastmem
  have hlastr : p1.getLast! ∈ r := ml1S2MemImpR L hL hgn hm hnf hlasts
  -- state-1 normalList 与 split.2 成员/无重
  have hn1 : normalList L hL (ntrans L N r x 1) := ml1NormalNtrans1 L hL hgn hm hnf
  have hff : findFaceDarts L (ly L r x) = findFaceDarts L x :=
    memFindFaceImpFacesEq hL.1 hyf
  have hf2mem : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2 ∈ ntrans L N r x 1 := by
    rw [← hff]
    exact Kepler.Text.Reduction5.sndMemRtran1 L hL hgn hm hnf
  have hf2nd : (splitNormalList L r (findFaceDarts L x) (ly L r x)
      (prevEl r (lz L N r x))).2.Nodup :=
    (List.nodup_flatten.mp hn1.1).1 _ hf2mem
  -- p1 的 LAST 与 d 同 FST
  have hf1 : p1.getLast!.1 = d.1 := by
    rw [Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf2mem hp1s2 hlastmem]
    exact (Kepler.Text.MoreLemma2PartsFst.partsFst L hL hn1 hf2mem hp1s2 hd1).symm
  -- LAST p1 ≠ LAST s2 = y
  have hneLast : p1.getLast! ≠ (ml1S2 L N r x).getLast! := by
    intro h
    have h1 : p1.getLast!.1 = (ly L r x).1 := by
      rw [h, ml1S2Last (r := r) (N := N) (x := x)]
    exact hdfst (hf1.symm.trans h1)
  have hneY : p1.getLast! ≠ ly L r x := by
    intro h
    exact hneLast (by rw [ml1S2Last (r := r) (N := N) (x := x)]; exact h)
  -- state-1 normal_condition
  have hneg1 : ¬(nextEl (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).2 p1.getLast!
      = fList L (eList p1.getLast!)) :=
    (Kepler.Text.Reduction5.normalConditionLastPartsChain L hL hn1
      hm.1.edgeNondegenerate hf2mem hp1s2 hlastmem).mpr rfl
  -- split.2 = s2 ++ betwn f y z
  have hnextPrev : nextEl r (prevEl r (lz L N r x)) = ztrans L N r x 0 := by
    rw [Kepler.Text.Reduction5.nextElInstEq, Kepler.Text.Reduction5.nextPrevId hrnd]
    rfl
  have hsplit2 : (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).2
      = ml1S2 L N r x ++ between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0) := by
    show (([nextEl r (prevEl r (lz L N r x))] ++
        (between r (nextEl r (prevEl r (lz L N r x))) (ly L r x) ++ [ly L r x]))
      ++ between (findFaceDarts L x) (ly L r x) (nextEl r (prevEl r (lz L N r x))))
      = ml1S2 L N r x ++ between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0)
    rw [hnextPrev]
    rfl
  -- nextEl 从 split.2 降到 s2（nextElCat1：s2 是 split.2 前缀）
  have hnext1 : nextEl (splitNormalList L r (findFaceDarts L x) (ly L r x)
        (prevEl r (lz L N r x))).2 p1.getLast!
      = nextEl (ml1S2 L N r x) p1.getLast! := by
    rw [hsplit2]
    exact Kepler.Text.TameSpine.nextElCat1
      (s := ml1S2 L N r x)
      (t := between (findFaceDarts L x) (ly L r x) (ztrans L N r x 0))
      hsnd hlasts hneLast
  -- nextEl 再从 s2 降到 r（nextCatBetwnSame：LAST p1 ∈ 弧 [z,y]）
  have hnext2 : nextEl (ml1S2 L N r x) p1.getLast! = nextEl r p1.getLast! :=
    Kepler.Text.TameSpine.nextCatBetwnSame r hrnd hyr hzr hzy.symm hlasts
      (by unfold ml1S2; rfl) hneY
  -- LAST p1 ∈ p（块首 FST 单射定位）
  obtain ⟨p', hp', hlastp'⟩ :=
    Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hlastr
  have hpfst : p1.getLast!.1 = p'.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp' hlastp'
  have hpd : d.1 = p.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hp hd
  have hpp : p' = p := by
    have hfst : p'.head!.1 = p.head!.1 := by
      rw [← hpfst, hf1]
      exact hpd
    exact List.inj_on_of_nodup_map
      (ml1PartsHeadFstNodup L hL hm hm.2.2.1) hp' hp hfst
  have hdlp : p1.getLast! ∈ p := by
    rw [← hpp]
    exact hlastp'
  refine (Kepler.Text.Reduction5.normalConditionLastPartsChain L hL hm.2.1
    hm.1.edgeNondegenerate hm.2.2.1 hp hdlp).mp ?_
  rw [← hnext2, ← hnext1]
  exact hneg1

/-- **W3a-1（HOL :2760，`LAST pz1 = LAST pz`）**：
f2 半列表中含 `z` 的块 `pz1` 的末元 = `parts L r` 中含 `z` 的块 `pz` 的末元。 -/
theorem ml1Pz1Last (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {pz : List Dart} (hpz : pz ∈ parts L r)
    (hzpz : ztrans L N r x 0 ∈ pz) :
    ∃ pz1 : List Dart, pz1 ∈ parts L (ml1S2 L N r x) ∧
      ztrans L N r x 0 ∈ pz1 ∧ pz1.getLast! = pz.getLast! := by
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hzs : ztrans L N r x 0 ∈ ml1S2 L N r x := (ml1S2Mem L N r x).1
  obtain ⟨pz1, hpz1, hzpz1⟩ :=
    Kepler.Text.MoreLemma2Naming.partsMemExists L hsnd hzs
  have hparts2 := ml1SplitSndParts L hL hgn hm hnf
  have hpz1s2 : pz1 ∈ parts L (splitNormalList L r (findFaceDarts L x)
      (ly L r x) (prevEl r (lz L N r x))).2 := by
    rw [hparts2]
    exact List.mem_append_left _ hpz1
  have hzyFst : (ztrans L N r x 0).1 ≠ (ly L r x).1 := by
    intro h
    exact ml1FstNe L hL hgn hm hnf h.symm
  exact ⟨pz1, hpz1, hzpz1,
    ml1PartEnd2 L hL hgn hm hnf hpz hpz1 hpz1s2 hzpz hzpz1 hzyFst⟩

/-- **W3a-2（HOL :2769–:2792）**：给定 `LAST pz1 = LAST pz`，
`pz1.getLast! ≠ s2.getLast!` 且 `nextEl s2 pz1.getLast! = nextEl r pz1.getLast!`。 -/
theorem ml1S2LastNe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    {pz pz1 : List Dart} (hpz : pz ∈ parts L r)
    (hpz1 : pz1 ∈ parts L (ml1S2 L N r x))
    (hzpz : ztrans L N r x 0 ∈ pz)
    (hlast : pz1.getLast! = pz.getLast!) :
    pz1.getLast! ≠ (ml1S2 L N r x).getLast! ∧
      nextEl (ml1S2 L N r x) pz1.getLast! = nextEl r pz1.getLast! := by
  obtain ⟨hyr, hzr, -, -, -, -, -, -, hzy⟩ := ml1SetupMem L hL hgn hm hnf
  have hrnd : r.Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hm.2.1.1 hm.2.2.1
  have hsnd : (ml1S2 L N r x).Nodup := ml1S2Uniq L hL hgn hm hnf
  have hzs : ztrans L N r x 0 ∈ ml1S2 L N r x := (ml1S2Mem L N r x).1
  have hsne : ml1S2 L N r x ≠ [] := List.ne_nil_of_mem hzs
  have hpne : pz ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ pz hpz
  have hp1ne : pz1 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L _ pz1 hpz1
  have hplastmem : pz.getLast! ∈ pz := Kepler.Text.TameSpine.aqs_getLastMem hpne
  have hp1lastmem : pz1.getLast! ∈ pz1 := Kepler.Text.TameSpine.aqs_getLastMem hp1ne
  have hlasts : pz1.getLast! ∈ ml1S2 L N r x :=
    ml1PartsMemImp L hsnd hsne hpz1 _ hp1lastmem
  -- LAST pz1 的 FST = z 的 FST
  have hfst1 : pz1.getLast!.1 = pz.head!.1 := by
    rw [hlast]
    exact Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpz hplastmem
  have hfst2 : (ztrans L N r x 0).1 = pz.head!.1 :=
    Kepler.Text.MoreLemma2PartsFst.partsFst L hL hm.2.1 hm.2.2.1 hpz hzpz
  have hyne : (ly L r x).1 ≠ (ztrans L N r x 0).1 :=
    fun h => ml1FstNe L hL hgn hm hnf h
  have hneY : pz1.getLast! ≠ ly L r x := by
    intro h
    have h1 : pz1.getLast!.1 = (ly L r x).1 := by
      rw [h]
    exact hyne ((h1.symm.trans hfst1).trans hfst2.symm)
  constructor
  · intro h
    exact hneY (by rw [h, ml1S2Last (r := r) (N := N) (x := x)])
  · exact Kepler.Text.TameSpine.nextCatBetwnSame r hrnd hyr hzr hzy.symm hlasts
      (by unfold ml1S2; rfl) hneY

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.ml1BracketUniq
#print axioms Kepler.Text.Reduction5.ml1S2Uniq
#print axioms Kepler.Text.Reduction5.ml1PartEnd2
#print axioms Kepler.Text.Reduction5.ml1Pz1Last
#print axioms Kepler.Text.Reduction5.ml1S2LastNe
