/-
  Kepler.Text.Reduction5J7W3a — J5-7 W3：z_y 族四件
  （HOL betwn_core0_z_y.hl:84 / :207 / :341 / :478）：

  · `memBetwnCore0ZY`   —— HOL `mem_betwn_core0_z_y`（:84）：
    `d ∈ betwn f zi ys ↔ d ∈ betwn r zi ys`（zi = ztrans i，ys = ytrans (i+1)）；
  · `lastBetwnCore0ZY`  —— HOL `last_betwn_core0_z_y`（:207）：
    两侧 betwn 的 `getLast!` 相等（LAST 的总化载体，同 W2b 先例）；
  · `betwnBetwnCore0ZY` —— HOL `betwn_betwn_core0_z_y`（:341）：
    `betwn f zi ys = betwn r zi ys`；
  · `finalBetwnCore0ZY` —— HOL `final_betwn_core0_z_y`（:478）：
    `betwn (core L r) (FST zi) (FST ys) = betwn (core L (find_face L x)) ...`。

  **路线（W2 的 indexf 层 + 逐位外延模式，HOL 四条均不照抄）**：
  1. 引擎 `betwnZYEq`：`betwnOrbit` 两侧 + 幂同步
     `betwnZtranYtransSucConstChain`（在库）逐位外延；长度只需
     `indexf zi ys r = indexf zi ys f`——r 侧由 `nextElnIndexf`（幂命中 + 界
     `< r.length`，后者经 `indexfZLtSizelYtran` + parts 基数/flatten 链）。
  2. `mem`/`last` 两件是引擎的直接推论（`rw`），不消费 HOL 的
     indexf_betwn_eq / betwn_mem / MEM_POWER_NEXT_EL 链。
  3. `final` 件仍走逐位：r 侧走步用 `nextPowerCoreYtran`（在库），
     c 侧 indexf 直接取 `indexf3FinalLemmas`（在库，免计数），
     f 侧 `coreFinalList` + `nextElMapApply` 私件同证重推导。
  **HOL 的 parts 边界事实（LAST pz = zi / ys = HD py）与
  aqs_fstHdMapBetwn/partsBetwn 链零消费**（W2d 勘误的延续）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5J7W1d
import Kepler.Text.Reduction5J7W1b
import Kepler.Text.Reduction5J5BetweenInst

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- `uniq (l.map f)` 下，`l.map f` 环上的 next_el 与原环经 f 对接
（J5M2Core 私有件 `nextElMapApply` 同证重推导）。 -/
private theorem nextElMapApplyC {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β]
    (f : α → β) {l : List α} (hnd : (l.map f).Nodup) {a : α} (ha : a ∈ l) :
    nextEl (l.map f) (f a) = f (nextEl l a) := by
  have hfa : f a ∈ l.map f := List.mem_map_of_mem ha
  have hilt : l.idxOf a < l.length := List.idxOf_lt_length_iff.mpr ha
  have hmlt : l.idxOf a < (l.map f).length := by rw [List.length_map]; exact hilt
  have hget : (l.map f)[l.idxOf a] = f a := by
    rw [List.getElem_map]
    exact congrArg f (Kepler.Text.TameLp.getElem_idxOf ha)
  have hidx : (l.map f).idxOf (f a) = l.idxOf a := by
    have h := hnd.idxOf_getElem (l.idxOf a) hmlt
    rw [hget] at h
    exact h
  rw [Kepler.Text.TameLp.nextEl_eq_getD hfa, hidx, List.length_map,
    Kepler.Text.TameLp.nextEl_eq_getD ha, List.getD_map]

/-- **W3 引擎**：z_y 弧上两侧 betwn 相等（HOL `betwn_betwn_core0_z_y` 的证体）：
`betwn f zi ys = betwn r zi ys`，zi = ztrans i、ys = ytrans (i+1)。 -/
private theorem betwnZYEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) (hk : transformCount L N r x = k)
    {i : ℕ} (hi : i + 1 < k)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hne : (ztrans L N r x i).1 ≠ (ytrans L N r x (i + 1)).1) :
    between f (ztrans L N r x i) (ytrans L N r x (i + 1))
      = between r (ztrans L N r x i) (ytrans L N r x (i + 1)) := by
  set zi := ztrans L N r x i with hzi
  set ys := ytrans L N r x (i + 1) with hyi
  -- 状态 i+1 非 final ⇒ i 非 final
  have hf2 : ¬ finalList L (rtrans L N r x (i + 1)) :=
    Kepler.Text.Reduction4.transformCount_not (i + 1) (by rw [hk]; exact hi)
  have hfI : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction5.finalListInduct i hf2
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hrne : r ≠ [] := List.ne_nil_of_mem hm.2.2.2.1
  -- 端点Membership
  have hziR : zi ∈ r := pnxvwfs2 L hL hgn haq i hfI hm
  have hysR : ys ∈ r := by
    have h := pnxvwfs1 L hL hgn haq (i + 1) hf2 hm
    rwa [← hyi] at h
  have hziF : zi ∈ f := by
    have h := Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm i
    rwa [← hzi, hfind] at h
  have hysF : ys ∈ f := by
    have h := Kepler.Text.MoreLemma2a23.ytranMeF L hL hm hfind.symm (i + 1)
    rwa [← hyi] at h
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  have hneD : zi ≠ ys := fun h => hne (by rw [h])
  -- 弧长上界：indexf zi ys f < r.length（经 parts 基数 + flatten）
  have hmltParts : indexf zi ys f < (parts L r).toFinset.card :=
    indexfZLtSizelYtran L hL hgn hres haq hm hf2 (hfind := hfind) (hw := hw)
  have hcard : (parts L r).toFinset.card = (parts L r).length :=
    List.toFinset_card_of_nodup (Kepler.Text.MoreLemma2Island2.uniqParts L hnd hrne)
  have hpartsLe : (parts L r).length ≤ r.length := by
    have h := sizeFlattenLe (parts L r) (Kepler.Text.MoreLemma2Island2.partsAllNonnil L r)
    rwa [Kepler.Text.MoreLemma2Island2.partsFlatten L hnd hrne] at h
  have hmLtR : indexf zi ys f < r.length := by
    rw [hcard] at hmltParts
    omega
  -- r 侧的幂命中 + indexf 唯一性
  have hpF : (nextEl f)^[indexf zi ys f] zi = ys := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine]
    exact Kepler.Text.TameSpine.indexfN hziF hysF hfnd
  have hpR : (nextEl r)^[indexf zi ys f] zi = ys := by
    have h := Kepler.Text.TameSpine.betwnZtranYtransSucConstChain L hL hgn haq hm i hf2
      hfind hw (n := indexf zi ys f) le_rfl
    have h' : (nextEl r)^[indexf zi ys f] zi = (nextEl f)^[indexf zi ys f] zi := by
      simpa only [hzi] using h
    exact h'.trans hpF
  have hpRdec : (@nextEl Dart instBEqOfDecidableEq r)^[indexf zi ys f] zi = ys := by
    rw [← Kepler.Text.Reduction5.iterateInstEq r zi (indexf zi ys f)]
    exact hpR
  have hidxr : indexf zi ys r = indexf zi ys f :=
    Kepler.Text.MoreLemma2Island1.nextElnIndexf hziR hysR hnd hpRdec hmLtR
  -- 长度 + 逐位收口
  have hlenf : (between f zi ys).length = indexf zi ys f - 1 := by
    rw [Kepler.Text.Reduction5.betweenInstEq f zi ys]
    exact sizeBetwn hfnd hziF hysF hneD
  have hlenr : (between r zi ys).length = indexf zi ys f - 1 := by
    rw [Kepler.Text.Reduction5.betweenInstEq r zi ys]
    rw [sizeBetwn hnd hziR hysR hneD, hidxr]
  refine List.ext_getElem ?_ (fun j hjf hjr => ?_)
  · rw [hlenf, hlenr]
  · rw [Kepler.Text.TameSpine.betwnOrbit hneD hfnd hziF hysF hjf,
      Kepler.Text.TameSpine.betwnOrbit hneD hnd hziR hysR hjr]
    rw [hlenf] at hjf
    have hle : j + 1 ≤ indexf zi ys f := by omega
    exact (Kepler.Text.TameSpine.betwnZtranYtransSucConstChain L hL hgn haq hm i hf2
      hfind hw (n := j + 1) hle).symm

/-- **W3-1：HOL `mem_betwn_core0_z_y`**（betwn_core0_z_y.hl:84）：
`d ∈ betwn f zi ys ↔ d ∈ betwn r zi ys`（zi = ztrans i，ys = ytrans (i+1)）。 -/
theorem memBetwnCore0ZY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) (hk : transformCount L N r x = k)
    {i : ℕ} (hi : i + 1 < k)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hne : (ztrans L N r x i).1 ≠ (ytrans L N r x (i + 1)).1)
    (d : Dart) :
    d ∈ between f (ztrans L N r x i) (ytrans L N r x (i + 1))
      ↔ d ∈ between r (ztrans L N r x i) (ytrans L N r x (i + 1)) := by
  rw [betwnZYEq L hL hgn hres haq hm hf hk hi hfind hw hne]

/-- **W3-2：HOL `last_betwn_core0_z_y`**（betwn_core0_z_y.hl:207）：
两侧 betwn 的末元相等（总化载体 `getLast!`，与 W2b `lastBetwnDY` 同款）。 -/
theorem lastBetwnCore0ZY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) (hk : transformCount L N r x = k)
    {i : ℕ} (hi : i + 1 < k)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hne : (ztrans L N r x i).1 ≠ (ytrans L N r x (i + 1)).1) :
    (between f (ztrans L N r x i) (ytrans L N r x (i + 1))).getLast!
      = (between r (ztrans L N r x i) (ytrans L N r x (i + 1))).getLast! := by
  rw [betwnZYEq L hL hgn hres haq hm hf hk hi hfind hw hne]

/-- **W3-3：HOL `betwn_betwn_core0_z_y`**（betwn_core0_z_y.hl:341）：
`betwn f zi ys = betwn r zi ys`（引擎 `betwnZYEq` 的公开形）。 -/
theorem betwnBetwnCore0ZY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) (hk : transformCount L N r x = k)
    {i : ℕ} (hi : i + 1 < k)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hne : (ztrans L N r x i).1 ≠ (ytrans L N r x (i + 1)).1) :
    between f (ztrans L N r x i) (ytrans L N r x (i + 1))
      = between r (ztrans L N r x i) (ytrans L N r x (i + 1)) :=
  betwnZYEq L hL hgn hres haq hm hf hk hi hfind hw hne

/-- **W3-4：HOL `final_betwn_core0_z_y`**（betwn_core0_z_y.hl:478）：
`betwn (core L r) (FST zi) (FST ys) = betwn (core L (find_face L x)) (FST zi) (FST ys)`。
逐位路线：r 侧走步 `nextPowerCoreYtran`、c 侧 indexf `indexf3FinalLemmas`、
f 侧 `coreFinalList` + `nextElMapApply` 私件。 -/
theorem finalBetwnCore0ZY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) (hk : transformCount L N r x = k)
    {i : ℕ} (hi : i + 1 < k)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hne : (ztrans L N r x i).1 ≠ (ytrans L N r x (i + 1)).1) :
    between (core L r) (ztrans L N r x i).1 (ytrans L N r x (i + 1)).1
      = between (core L (findFaceDarts L x)) (ztrans L N r x i).1
          (ytrans L N r x (i + 1)).1 := by
  rw [hfind]
  set zi := ztrans L N r x i with hzi
  set ys := ytrans L N r x (i + 1) with hyi
  have hf2 : ¬ finalList L (rtrans L N r x (i + 1)) :=
    Kepler.Text.Reduction4.transformCount_not (i + 1) (by rw [hk]; exact hi)
  have hfI : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction5.finalListInduct i hf2
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hziR : zi ∈ r := pnxvwfs2 L hL hgn haq i hfI hm
  have hysR : ys ∈ r := by
    have h := pnxvwfs1 L hL hgn haq (i + 1) hf2 hm
    rwa [← hyi] at h
  have hziF : zi ∈ f := by
    have h := Kepler.Text.TameSpine.ztranMeFChain L hL hgn haq hm i
    rwa [← hzi, hfind] at h
  have hysF : ys ∈ f := by
    have h := Kepler.Text.MoreLemma2a23.ytranMeF L hL hm hfind.symm (i + 1)
    rwa [← hyi] at h
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  -- core r：无重 + 端点membership
  have hc_nd : (core L r).Nodup := by
    have hq := Kepler.Text.MoreLemma2a23.quotientAllUniq L hL hm
    refine hq (core L r) ?_
    rw [Kepler.Text.MoreLemma2Island1.quotientListCore]
    exact List.mem_map.mpr ⟨r, hm.2.2.1, rfl⟩
  have hzi1c : zi.1 ∈ core L r := memCore (L := L) hL hgn hm hziR hf
  have hys1c : ys.1 ∈ core L r := memCore (L := L) hL hgn hm hysR hf
  -- f final ⇒ core f = map FST f
  have hfinK : finalList L (rtrans L N r x k) :=
    finalListTransformCount L hL hgn haq hm (t := k) hk
  have hmK : Kepler.Text.ChainLists.markedList L hL
      (ntrans L N r x k) (rtrans L N r x k) x := haq hgn N r x hm k
  have hrndK : (rtrans L N r x k).Nodup :=
    (List.nodup_flatten.mp hmK.2.1.1).1 (rtrans L N r x k) hmK.2.2.1
  have hxrK : x ∈ rtrans L N r x k := hmK.2.2.2.1
  have hxd : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  obtain ⟨nrot, hrot⟩ :=
    Kepler.Text.Reduction5.finalListRot hL hfinK hxrK hrndK hxd
  have hf_rot : f = (rtrans L N r x k).rotate nrot := (hrot.trans hfind).symm
  have hfinF : finalList L f := by
    intro y hy
    have hyK : y ∈ rtrans L N r x k := by
      rw [hf_rot] at hy
      exact List.mem_rotate.mp hy
    rw [hfinK y hyK, hf_rot]
    exact (Kepler.Text.Reduction5.nextElRotate hrndK nrot y).symm
  have hall : ∀ y ∈ f, y ∈ listOfDarts L := by
    intro y hy
    exact Kepler.Text.TameLp.mem_darts_of_mem_findFace L (d := x)
      (by rw [hfind]; exact hy)
  have hcf : core L f = f.map (fun y : Dart => y.1) :=
    Kepler.Text.TameSpine.coreFinalList L hL hall hm.1.edgeNondegenerate hfinF hfnd
  have hmapnd : (f.map (fun y : Dart => y.1)).Nodup := by
    rw [← hfind]
    exact uniqFstFindFace L hL hgn hres hm
  have hzi1cf : zi.1 ∈ core L f := by
    rw [hcf]
    exact List.mem_map.mpr ⟨zi, hziF, rfl⟩
  have hys1cf : ys.1 ∈ core L f := by
    rw [hcf]
    exact List.mem_map.mpr ⟨ys, hysF, rfl⟩
  have hcf_nd : (core L f).Nodup := hcf ▸ hmapnd
  -- r 侧走步（在库 nextPowerCoreYtran）+ f 侧走步
  have hwalkR : ∀ n : ℕ, n ≤ indexf zi ys f →
      (nextEl (core L r))^[n] zi.1 = ((nextEl r)^[n] zi).1 := by
    intro n hn
    exact Kepler.Text.TameSpine.nextPowerCoreYtran L hL hgn haq hm (hk := hk) (i := i) hi
      (hfind := hfind) (hw := hw) (zi := ztrans L N r x i) (hzi := rfl)
      (yi := ytrans L N r x (i + 1)) (hyi := rfl) (n := n) hn
  have hnextMap : ∀ a ∈ f,
      nextEl (f.map (fun y : Dart => y.1)) a.1 = (nextEl f a).1 := by
    intro a ha
    simpa using nextElMapApplyC (f := fun y : Dart => y.1) hmapnd ha
  have hwalkF : ∀ n : ℕ, (nextEl (core L f))^[n] zi.1 = ((nextEl f)^[n] zi).1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      have hxif : (nextEl f)^[n] zi ∈ f := Kepler.Text.TameSpine.memPowerNextEl hziF n
      rw [hcf, hnextMap ((nextEl f)^[n] zi) hxif, Function.iterate_succ_apply']
  -- 两侧 indexf = indexf zi ys f
  have hidxc : indexf zi.1 ys.1 (core L r) = indexf zi ys f := by
    have h := indexf3FinalLemmas L hL hgn hres haq hm hk hi
    rwa [hfind] at h
  have hltcf : indexf zi ys f < (core L f).length := by
    rw [hcf, List.length_map]
    exact indexfLtSizel hziF hysF
  have hpcf : (nextEl (core L f))^[indexf zi ys f] zi.1 = ys.1 := by
    rw [hwalkF (indexf zi ys f)]
    have hpF : (nextEl f)^[indexf zi ys f] zi = ys := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine]
      exact Kepler.Text.TameSpine.indexfN hziF hysF hfnd
    rw [hpF]
  have hidxcf : indexf zi.1 ys.1 (core L f) = indexf zi ys f :=
    Kepler.Text.MoreLemma2Island1.nextElnIndexf hzi1cf hys1cf hcf_nd hpcf hltcf
  -- 长度 + 逐位收口
  have hne1 : zi.1 ≠ ys.1 := hne
  have hlenr : (between (core L r) zi.1 ys.1).length = indexf zi ys f - 1 := by
    rw [sizeBetwn hc_nd hzi1c hys1c hne1, hidxc]
  have hlenf : (between (core L f) zi.1 ys.1).length = indexf zi ys f - 1 := by
    rw [sizeBetwn hcf_nd hzi1cf hys1cf hne1, hidxcf]
  refine List.ext_getElem ?_ (fun j hj1 hj2 => ?_)
  · rw [hlenr, hlenf]
  · rw [Kepler.Text.TameSpine.betwnOrbit hne1 hc_nd hzi1c hys1c hj1,
      Kepler.Text.TameSpine.betwnOrbit hne1 hcf_nd hzi1cf hys1cf hj2]
    rw [hlenr] at hj1
    have hle : j + 1 ≤ indexf zi ys f := by omega
    rw [hwalkR (j + 1) hle, hwalkF (j + 1)]
    exact congrArg (fun z : Dart => z.1)
      (Kepler.Text.TameSpine.betwnZtranYtransSucConstChain L hL hgn haq hm i hf2
        hfind hw (n := j + 1) hle)

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction5.memBetwnCore0ZY
#print axioms Kepler.Text.Reduction5.lastBetwnCore0ZY
#print axioms Kepler.Text.Reduction5.betwnBetwnCore0ZY
#print axioms Kepler.Text.Reduction5.finalBetwnCore0ZY
