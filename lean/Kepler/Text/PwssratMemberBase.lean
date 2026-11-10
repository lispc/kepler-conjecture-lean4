/-
  Kepler.Text.PwssratMemberBase — 无撞铺装波 patch1：PWSSRAT member 基座
  （next_el_rotate_to_eq → f_eq_next_el_x → l_y_rep_power → ytrans_mem_rtrans）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）────────
  │ PWSSRAT.hl:122 `next_el_rotate_to_eq` → nextElRotateToEq
  │ PWSSRAT.hl:160 `f_eq_next_el_x`       → fEqNextElX（rtrans 形）
  │ PWSSRAT.hl:263 `l_y_rep_power`        → lyNextElPow
  │ PWSSRAT.hl:275 `ytrans_mem_rtrans`    → ytransMemRtrans
  │ patch5 续：HQYMRTX1_list（tame_list.hl:10165）+ mem_ztrans_rtrans
  │ （PWSSRAT:298）/ z_not_eq_ytrans（:320）——hs 槽按裁决 a 显式化，
  │ 变换后 loop 的 hs 由本文件 sListEqOfMarked 现产（DIFFERS 见 §3）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与折算 ──────────────────────────────────────────────────
  │ `rotate_to` ↦ Reduction3.rotateTo；`split_at` ↦ Graphs.splitAt
  │ （patch_p2pre1 底座：splitAtRec 分解/sndEmptyIndexl/hdFstSplit）；
  │ `next_el` ↦ nextEl；`f_list` ↦ fList；`l'm`/`l'y` ↦
  │ Reduction5.lm/ly；`ytrans` ↦ Reduction5.ytrans；`ITER` ↦ f^[n]；
  │ `min_not_eq_imp_eq_at` ↦ MoreLemma2Aux.minNotEqImpEq（at 形已落）；
  │ `MEM_POWER_NEXT_EL` ↦ MoreLemma2Island1.memNextElIterate；
  │ AQIUNPP3 ↦ AqiunppSlot（Subseg9 槽）+ transform_list_power_rep
  │ 链侧 defs rfl 吸收（rtrans = iterate 投影）。
  │ 环安全：imports = PwssratRotateBase（patch_p2pre1 底座）+
  │ Reduction4Subseg9（AqiunppSlot）+ MoreLemma2Aux + Reduction5 +
  │ ChainMarkedTranslate（patch5 链侧 facade）+ MoreLemma2a23。
  │ 直接 import 零 TameSpine；ChainMarkedTranslate 闭包含 TameList17
  │ （hs/loop 载体所必需，DIFFERS 见 DELIVERY）。
  │ 零 axiom/sorry/admit/native_decide；主仓 tracked 零改动。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.PwssratRotateBase
import Kepler.Text.Reduction4Subseg9
import Kepler.Text.MoreLemma2Aux
import Kepler.Text.Reduction5Tav2
import Kepler.Text.ChainMarkedTranslate
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph splitAt splitAtRec)
open Kepler.Assembly (GoodList nextEl fList listOfDarts)
open Kepler.Text.Reduction3 (rotateTo)
open Kepler.Text.Reduction5 (Dart lm ly lz ztrans ytrans rtrans ntrans finalList
  transformAssumptionV2)
open Kepler.Text.ChainLists (markedList normalList sList)
open Kepler.Text.Reduction5 (quotientList)
open Kepler.Text.ChainMarkedQ (loopOfList loopFamilyOfList normalListIsNormalFamily)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl darts_hypermapOfList
  faceMap_hypermapOfList fList_mem_darts)

/-! ## §1 `next_el_rotate_to_eq`（PWSSRAT:122；rotate 件本体）

HOL：`!r. MEM x r ∧ uniq r ⇒ next_el r x = next_el (rotate_to r x) x`。
证明 = splitAtRec 分解（patch_p2pre1）+ 两支（x 末位 / 非末位）逐支 idxOf 算术。 -/

/-- 分解决策位：`x ∈ r`、Nodup ⇒ `x ∉ fst(splitAt x r)`。 -/
private theorem notMem_splitAt_fst {α : Type*} [BEq α] [LawfulBEq α] {x : α}
    {r : List α} (hmem : x ∈ r) (hnd : r.Nodup) :
    x ∉ (splitAt x r).1 := by
  obtain ⟨fst, hreq, hfst⟩ := splitAtRec_exists_append r [] hmem (by simp)
  have hfst' : (splitAtRec x [] r).1 = fst := by rw [hfst, List.nil_append]
  have hnd' : (fst ++ x :: (splitAtRec x [] r).2).Nodup := by
    rw [← hreq]
    exact hnd
  have hdis : List.Disjoint fst (x :: (splitAtRec x [] r).2) :=
    List.disjoint_of_nodup_append hnd'
  rw [show (splitAt x r).1 = fst from hfst']
  intro hc
  exact hdis hc (List.mem_cons.mpr (Or.inl rfl))

/-- `x` 的 `idxOf` 值（分解形）：`r = fst ++ x :: snd`、`x ∉ fst`
⇒ `idxOf x r = fst.length`。 -/
private theorem idxOf_splitAt_fst {α : Type*} [BEq α] [LawfulBEq α] {x : α}
    {r : List α} (hmem : x ∈ r) (hnd : r.Nodup) :
    r.idxOf x = (splitAt x r).1.length := by
  obtain ⟨fst, hreq, hfst⟩ := splitAtRec_exists_append r [] hmem (by simp)
  have hfst' : (splitAtRec x [] r).1 = fst := by rw [hfst, List.nil_append]
  have hxf : x ∉ fst := by
    have h := notMem_splitAt_fst hmem hnd
    rwa [show (splitAt x r).1 = fst from hfst'] at h
  rw [show (splitAt x r).1 = fst from hfst', hreq,
    List.idxOf_append_of_notMem hxf,
    List.idxOf_cons_eq (l := (splitAtRec x [] r).2) rfl]
  simp

/-- **HOL `next_el_rotate_to_eq`**（PWSSRAT.hl:122-:158）。 -/
theorem nextElRotateToEq {α : Type} [BEq α] [LawfulBEq α] {r : List α} {x : α}
    (hmem : x ∈ r) (hnd : r.Nodup) :
    nextEl r x = nextEl (rotateTo r x) x := by
  obtain ⟨fst, hreq, hfst⟩ := splitAtRec_exists_append r [] hmem (by simp)
  have hsplit1 : (splitAt x r).1 = fst := by
    rw [show (splitAt x r).1 = (splitAtRec x [] r).1 from rfl, hfst,
      List.nil_append]
  have hsplit2 : (splitAt x r).2 = (splitAtRec x [] r).2 := rfl
  have hxf : x ∉ fst := by
    rw [← hsplit1]
    exact notMem_splitAt_fst hmem hnd
  have hidx : r.idxOf x = fst.length := by
    rw [← hsplit1]
    exact idxOf_splitAt_fst hmem hnd
  have hlen : r.length = fst.length + 1 + (splitAtRec x [] r).2.length := by
    have h := congrArg List.length hreq
    simp [List.length_append, List.length_cons] at h
    omega
  by_cases hsnd : (splitAtRec x [] r).2 = []
  · -- x 位于末位：两侧 nextEl 都落到 r 的头部
    have hlen1 : r.length = fst.length + 1 := by
      rw [hlen, hsnd]
      simp
    have hidxlast : r.idxOf x = r.length - 1 := by
      rw [hidx, hlen1]
      omega
    rw [nextEl, if_pos hidxlast]
    -- rotateTo r x = x :: fst
    have hrot : rotateTo r x = x :: fst := by
      unfold rotateTo
      rw [hsplit1, hsplit2, hsnd, List.singleton_append]
    rw [hrot]
    have hnotlast : ¬ ((x :: fst).idxOf x = (x :: fst).length - 1) ∨
        fst = [] := by
      by_cases hf : fst = []
      · exact Or.inr hf
      · left
        intro hc
        rw [List.idxOf_cons_self] at hc
        simp at hc
        exact hf (List.length_eq_zero_iff.mp hc.symm)
    rcases hnotlast with hn | hf
    · rw [nextEl, if_neg hn, List.idxOf_cons_self, Nat.zero_add]
      -- getD 1 (x::fst) = fst.headD x；r.headD x 同
      have hgetD : (x :: fst).getD 1 x = fst.headD x := by
        cases fst with
        | nil => rfl
        | cons b bs => rfl
      rw [hgetD]
      -- r.headD x = fst.headD x（r = fst ++ [x]，fst ≠ []）
      have hf : fst ≠ [] := by
        intro hc
        exact hn (by rw [hc]; simp)
      rw [hreq, hsnd]
      cases fst with
      | nil => exact absurd rfl hf
      | cons b bs => rfl
    · -- fst = []：r = [x]，两侧同为 x
      subst hf
      rw [hreq, hsnd, List.nil_append]
      simp [nextEl]
  · -- x 非末位：两侧 nextEl 都落到 x 的后继
    have hlen2 : r.length - 1 = fst.length + (splitAtRec x [] r).2.length := by
      rw [hlen]
      have : 0 < (splitAtRec x [] r).2.length :=
        List.length_pos_iff.mpr hsnd
      omega
    have hnotlast : ¬ (r.idxOf x = r.length - 1) := by
      rw [hidx, hlen2]
      have : 0 < (splitAtRec x [] r).2.length :=
        List.length_pos_iff.mpr hsnd
      omega
    rw [nextEl, if_neg hnotlast, hidx]
    -- 左侧 getD = snd.headD
    have hleft : r.getD (fst.length + 1) x =
        (splitAtRec x [] r).2.headD x := by
      have hg := congrArg (fun s => s.getD (fst.length + 1) x) hreq
      rw [hg, List.getD_append_right (h := by omega)]
      rw [show fst.length + 1 - fst.length = 1 from by omega]
      cases h2 : (splitAtRec x [] r).2 with
      | nil => exact absurd h2 hsnd
      | cons b bs => rfl
    rw [hleft]
    -- rotateTo r x = x :: (snd ++ fst)
    have hrot : rotateTo r x = x :: ((splitAtRec x [] r).2 ++ fst) := by
      unfold rotateTo
      rw [hsplit1, hsplit2, List.cons_append]
    rw [hrot, nextEl]
    have hnotlast2 : ¬ ((x :: ((splitAtRec x [] r).2 ++ fst)).idxOf x =
        (x :: ((splitAtRec x [] r).2 ++ fst)).length - 1) := by
      intro hc
      rw [List.idxOf_cons_self] at hc
      rw [List.length_cons, List.length_append] at hc
      have hpos : 0 < (splitAtRec x [] r).2.length :=
        List.length_pos_iff.mpr hsnd
      omega
    rw [if_neg hnotlast2, List.idxOf_cons_self, Nat.zero_add]
    have hright : (x :: ((splitAtRec x [] r).2 ++ fst)).getD 1 x =
        (splitAtRec x [] r).2.headD x := by
      cases h2 : (splitAtRec x [] r).2 with
      | nil => exact absurd h2 hsnd
      | cons b bs => rfl
    rw [hright]

/-! ## §2 member 链快件（f_eq_next_el_x / l_y_rep_power / ytrans_mem_rtrans） -/

/-- **HOL `f_eq_next_el_x`**（PWSSRAT.hl:160-:174，rtrans 形）：
`fList L x = nextEl (rotateTo (rtrans L N r x i) x) x`。
证明 = AqiunppSlot 变换后 markedList 第 6 槽（nextEl (rtrans i) x = fList x）
+ `← nextElRotateToEq`。 -/
theorem fEqNextElX (L : fgraph ℕ) (hL : GoodList L)
    (haq : AqiunppSlot L hL)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : markedList L hL N r x) :
    fList L x = nextEl (rotateTo (rtrans L N r x i) x) x := by
  have hmk := haq hgn N r x hm i
  have hN := hmk.2.1
  have hrnd : (rtrans L N r x i).Nodup :=
    Kepler.Text.MoreLemma2Island1.uniqFlattenUniq hN.1 hmk.2.2.1
  have hxr : x ∈ rtrans L N r x i := hmk.2.2.2.1
  rw [← nextElRotateToEq hxr hrnd]
  exact (hmk.2.2.2.2.2.1).symm

/-- **HOL `l_y_rep_power`**（PWSSRAT.hl:263-:273）：
`fList L x = nextEl r x ⇒ ly L r x = (nextEl r)^[lm L r x + 1] x`。 -/
theorem lyNextElPow (L : fgraph ℕ) {r : List Dart} {x : Dart}
    (hteth : fList L x = nextEl r x) :
    Kepler.Text.Reduction5.ly L r x = (nextEl r)^[lm L r x + 1] x := by
  have hset : {m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)}
      = {m : ℕ | (nextEl r) ((nextEl r) ((nextEl r)^[m] x))
          ≠ fList L ((nextEl r) ((nextEl r)^[m] x))} := by
    ext m
    simp only [Set.mem_setOf_eq]
    have h1 : (nextEl r)^[m + 2] x = (nextEl r) ((nextEl r) ((nextEl r)^[m] x)) := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h2 : (nextEl r)^[m + 1] x = (nextEl r) ((nextEl r)^[m] x) := by
      rw [Function.iterate_succ_apply']
    rw [h1, h2]
  have h := Kepler.Text.MoreLemma2Aux.minNotEqImpEq (nextEl r) (fList L) x
    (n := lm L r x) (by rw [← hset]; rfl) (lm L r x) le_rfl
  rw [← hteth] at h
  rw [Function.iterate_succ] at h
  show (fList L)^[lm L r x + 1] x = (nextEl r)^[lm L r x + 1] x
  rw [Function.iterate_succ, Function.iterate_succ]
  exact h.symm

/-- **HOL `ytrans_mem_rtrans`**（PWSSRAT.hl:275-:296）。 -/
theorem ytransMemRtrans (L : fgraph ℕ) (hL : GoodList L)
    (haq : AqiunppSlot L hL)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : markedList L hL N r x) :
    ytrans L N r x i ∈ rtrans L N r x i := by
  have hmk := haq hgn N r x hm i
  have hxr : x ∈ rtrans L N r x i := hmk.2.2.2.1
  have hteth : fList L x = nextEl (rtrans L N r x i) x :=
    (hmk.2.2.2.2.2.1).symm
  show Kepler.Text.Reduction5.ly L (rtrans L N r x i) x ∈ rtrans L N r x i
  rw [lyNextElPow L hteth]
  have key : ∀ m : ℕ,
      (nextEl (rtrans L N r x i))^[m] x ∈ rtrans L N r x i := by
    intro m
    induction m with
    | zero => simpa using hxr
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact Kepler.Text.TameLp.nextEl_mem_of_mem ih
  exact key _

/-! ## §3 `HQYMRTX1_list`（tame_list.hl:10165）链层本体 + 连锁两件（PWSSRAT:298/:320）

HOL `HQYMRTX1_list` 的证体 = `Hypermap.lemmaHQYMRTX`（`hqymrtx`，Hypermap.lean:10504）
经 `marked_translate` 运输。链层载体：
`ChainMarkedTranslate.markedTranslate`（八合取，`hs : sList = sListSpine` 槽）+
`ChainMarkedQ.normalListIsNormalFamily` 供 `hnf`。

┌─ DIFFERS（交编排者知悉）────────────────────────────────────────
│ ① `hs` 槽按裁决 a 显式化：`sList L r x = sListSpine L r x`
│    （`lm` 的 minNum/epsilon 与 `lMSpine` 的 sInf 只在极小集空时分叉；
│    链侧全树无生产者，生产者落地本件一行消槽）。
│ ② `hunL : ∀ l ∈ L, l.Nodup`（HOL `all uniq L`）为独立前提：`GoodList`
│    只给 `(L.map listPairs).flatten` Nodup；反例 `[[1,2,1,3]]` 的
│    listPairs 四对互异而面表非 Nodup（GoodListDefs:72；与
│    ChainMarkedTranslate 头注 ① 同口径）。原工单「~10 行小证」为误判
│    （ERRATA，见 DELIVERY）。
│ ③ `mem_ztrans_rtrans`/`z_not_eq_ytrans` 的 HOL 前提
│    `transform_assumption_v2 L` 按 patch4 `ytransMemRtrans` 同一口径
│    折算为 `AqiunppSlot L hL`（全 i 的变换保持；HOL 证体同用 AQIUNPP3）。
│ ④ 变换后 loop 的 `hs` 槽由本文件 `sListEqOfMarked` 现产（§3.2），
│    故两连锁件不新增 `sList` 前提。
└────────────────────────────────────────────────────────────────
-/

/-! ### §3.1 载体小件（loop darts 折算 / faceMap 幂） -/

/-- `loopOfList r` 的 darts 就是 `r`（`r` Nodup 非空时走真分支；junk 支不可达）。 -/
private theorem memLoopOfListDarts {r : List Dart}
    (hrnd : r.Nodup) (hrne : r ≠ []) (z : Dart) :
    z ∈ r ↔ z ∈ (loopOfList r).darts := by
  show z ∈ r ↔ z ∈ (Kepler.Text.TameSpine.loopOfListSpine r).darts
  rw [Kepler.Text.TameSpine.loopOfListSpine_real hrnd hrne]
  exact List.mem_toFinset.symm

/-- `faceMap` 幂 = `fList` 迭代（HOL `face_map_list_power`；链侧重推：
`faceMap_hypermapOfList` + `fList_mem_darts` 归纳）。 -/
theorem faceMapListPowerChain (L : fgraph ℕ) (hL : GoodList L) (i : ℕ) {d : Dart}
    (hd : d ∈ listOfDarts L) :
    ((hypermapOfList L hL).faceMap ^ i) d = (fList L)^[i] d := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    have hdi : ∀ j : ℕ, (fList L)^[j] d ∈ listOfDarts L := by
      intro j
      induction j with
      | zero => simpa using hd
      | succ k ihk =>
        rw [Function.iterate_succ_apply']
        exact fList_mem_darts hL.1 ihk
    have hmem : (fList L)^[i] d ∈ (↑(hypermapOfList L hL).darts : Set Dart) := by
      rw [darts_hypermapOfList]
      exact hdi i
    rw [faceMap_hypermapOfList L hL (Finset.mem_coe.mp hmem),
      Function.iterate_succ_apply']

/-! ### §3.2 变换后 loop 的 `sList` 槽生产（`lm` 极小集非空 → `lm = lMSpine`） -/

/-- `minNum`（`Classical.epsilon`）的最小元规格（同证重推导）。 -/
private theorem minNumSpec {S : Set ℕ} (hne : S.Nonempty) :
    Kepler.Text.Reduction5.minNum S ∈ S ∧
      ∀ n ∈ S, Kepler.Text.Reduction5.minNum S ≤ n := by
  classical
  obtain ⟨m₀, hm₀⟩ := hne
  have hex : ∃ m : ℕ, m ∈ S := ⟨m₀, hm₀⟩
  have hmin : Nat.find hex ∈ S ∧ ∀ n ∈ S, Nat.find hex ≤ n :=
    ⟨Nat.find_spec hex, fun n hn => Nat.find_min' hex hn⟩
  exact Classical.epsilon_spec (p := fun m => m ∈ S ∧ ∀ n ∈ S, m ≤ n)
    ⟨Nat.find hex, hmin⟩

/-- `lm = lMSpine`（极小集非空时 `minNum` 与 `sInf` 同取最小元）。 -/
private theorem lmEqLMSpine (L : fgraph ℕ) {r : List Dart} {d : Dart}
    (hne : ({m : ℕ | (nextEl r)^[m + 2] d
      ≠ fList L ((nextEl r)^[m + 1] d)}).Nonempty) :
    lm L r d = Kepler.Text.TameSpine.lMSpine L r d := by
  show Kepler.Text.Reduction5.minNum
      {m : ℕ | (nextEl r)^[m + 2] d ≠ fList L ((nextEl r)^[m + 1] d)}
    = sInf {m : ℕ | (nextEl r)^[m + 2] d ≠ fList L ((nextEl r)^[m + 1] d)}
  exact le_antisymm ((minNumSpec hne).2 _ (Nat.sInf_mem hne))
    (Nat.sInf_le (minNumSpec hne).1)

/-- `lm` 的极小集非空：`~final_list L r` + `next_el r d = f_list L d` + `d ∈ r`
+ `r` 无重复。反证：若对所有 `m` 等式都成立，沿 `next_el` 轨道
（`indexfN` 定位到反例 `z`）可得 `f_list z = next_el r z`，与 `~final_list` 矛盾。
（同证重推导 ChainMarkedTranslate 私件 `lmSetNonempty`。） -/
private theorem lmSetNonempty (L : fgraph ℕ) {r : List Dart} {d : Dart}
    (hd : d ∈ r) (hr1 : r.Nodup) (hnext : nextEl r d = fList L d)
    (hf : ¬ finalList L r) :
    ({m : ℕ | (nextEl r)^[m + 2] d ≠ fList L ((nextEl r)^[m + 1] d)}).Nonempty := by
  by_contra hcon
  have hall : ∀ m : ℕ, (nextEl r)^[m + 2] d = fList L ((nextEl r)^[m + 1] d) := by
    intro m
    by_contra hc
    exact hcon ⟨m, hc⟩
  simp only [finalList] at hf
  push Not at hf
  obtain ⟨z, hzr, hz⟩ := hf
  have hz1 : (nextEl r)^[Kepler.Text.TameSpine.indexf d z r] d = z :=
    Kepler.Text.TameSpine.indexfN hd hzr hr1
  rcases Nat.eq_zero_or_pos (Kepler.Text.TameSpine.indexf d z r) with hk | hk
  · rw [hk] at hz1
    simp only [Function.iterate_zero_apply] at hz1
    exact hz (by rw [← hz1, hnext])
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
    have e1 : z = (nextEl r)^[j + 1] d := by rw [← hz1, hj]
    have h2 : (nextEl r)^[j + 2] d = nextEl r ((nextEl r)^[j + 1] d) :=
      Function.iterate_succ_apply' (nextEl r) (j + 1) d
    have hstep := hall j
    rw [h2, ← e1] at hstep
    exact hz hstep.symm

/-- `markedList` + `~final_list` ⇒ `sList = sListSpine`（变换后 loop 的 `hs` 槽生产：
`normalList` 给 `r.Nodup`，`lmSetNonempty` 给极小集非空，`lm = lMSpine` 换元）。 -/
private theorem sListEqOfMarked (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hf : ¬ finalList L r) :
    sList L r x = Kepler.Text.TameSpine.sListSpine L r x := by
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hnext : nextEl r x = fList L x := hm.2.2.2.2.2.1
  have hlm : lm L r x = Kepler.Text.TameSpine.lMSpine L r x :=
    lmEqLMSpine L (lmSetNonempty L hm.2.2.2.1 hrnd hnext hf)
  unfold sList Kepler.Text.TameSpine.sListSpine
  rw [hlm, List.range'_eq_map_range, List.map_map]
  congr 1
  funext i
  show (fList L)^[1 + i] x = (fList L)^[i + 1] x
  rw [Nat.add_comm 1 i]

/-! ### §3.3 `HQYMRTX1_list` 本体（tame_list.hl:10165-:10186） -/

/-- **HOL `HQYMRTX1_list`**（tame_list.hl:10165）链层形：
`l'z L N r x ∈ r` 且 `l'z ≠ (f_list L)^i x`（`1 ≤ i ≤ l'm + 1`）。 -/
theorem hqymrtx1List (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hf : ¬ finalList L r)
    (hs : sList L r x = Kepler.Text.TameSpine.sListSpine L r x) :
    lz L N r x ∈ r ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ lm L r x + 1 → lz L N r x ≠ (fList L)^[i] x := by
  obtain ⟨hM_eq, -, -, -, hZ_eq, hmark, hLnot, -⟩ :=
    Kepler.Text.ChainMarkedTranslate.markedTranslate L hL hgn hunL hm hf hs
  have hnf : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfList N) :=
    normalListIsNormalFamily L hL hgn hm.1 hm.2.1
  obtain ⟨hzDarts, hne⟩ :=
    (hypermapOfList L hL).hqymrtx (hmark hnf) hLnot
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hrne : r ≠ [] := hm.2.1.2.1 r hm.2.2.1
  have hxD : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  refine ⟨?_, ?_⟩
  · have hzD : lz L N r x ∈ (loopOfList r).darts := by
      rw [← hZ_eq]
      exact hzDarts
    exact (memLoopOfListDarts hrnd hrne _).mpr hzD
  · intro i hi1 hi2 hcon
    have hi2' : i ≤ (hypermapOfList L hL).hypM (loopFamilyOfList N)
        (loopOfList r) x + 1 := by
      rw [hM_eq]
      exact hi2
    refine (hne i hi1 hi2') ?_
    rw [hZ_eq, faceMapListPowerChain L hL i hxD]
    exact hcon

/-! ### §3.4 连锁两件（PWSSRAT:298 / :320） -/

/-- **HOL `mem_ztrans_rtrans`**（PWSSRAT.hl:298-:318）链层形：
`ztrans L N r x i ∈ rtrans L N r x i`——`hqymrtx1List` 首合取在变换后 loop
（`markedList` 由 `AqiunppSlot` 供给；变换后 `sList` 槽由 `sListEqOfMarked` 现产）。 -/
theorem memZtransRtrans (L : fgraph ℕ) (hL : GoodList L)
    (haq : AqiunppSlot L hL)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : markedList L hL N r x)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    ztrans L N r x i ∈ rtrans L N r x i := by
  have hm' : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x :=
    haq hgn N r x hm i
  exact (hqymrtx1List L hL hgn hunL hm' hf (sListEqOfMarked L hL hm' hf)).1

/-- **HOL `z_not_eq_ytrans`**（PWSSRAT.hl:320-:343）链层形：
`ztrans ≠ ytrans`——`hqymrtx1List` 第二合取取 `i = l'm + 1`（`ytrans = ly` 定义）。 -/
theorem zNotEqYtrans (L : fgraph ℕ) (hL : GoodList L)
    (haq : AqiunppSlot L hL)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : markedList L hL N r x)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    ztrans L N r x i ≠ ytrans L N r x i := by
  have hm' : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x :=
    haq hgn N r x hm i
  have hne := (hqymrtx1List L hL hgn hunL hm' hf (sListEqOfMarked L hL hm' hf)).2
  intro hcon
  refine hne (lm L (rtrans L N r x i) x + 1) (by omega) le_rfl ?_
  show ztrans L N r x i = (fList L)^[lm L (rtrans L N r x i) x + 1] x
  rw [hcon]
  rfl

end Kepler.Text.Reduction4Idx

/-! 公理审计锚。 -/
#print axioms Kepler.Text.Reduction4Idx.nextElRotateToEq
#print axioms Kepler.Text.Reduction4Idx.fEqNextElX

#print axioms Kepler.Text.Reduction4Idx.lyNextElPow
#print axioms Kepler.Text.Reduction4Idx.ytransMemRtrans

#print axioms Kepler.Text.Reduction4Idx.faceMapListPowerChain
#print axioms Kepler.Text.Reduction4Idx.hqymrtx1List
#print axioms Kepler.Text.Reduction4Idx.memZtransRtrans
#print axioms Kepler.Text.Reduction4Idx.zNotEqYtrans
