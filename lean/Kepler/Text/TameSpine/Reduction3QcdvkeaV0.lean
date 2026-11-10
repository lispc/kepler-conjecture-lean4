/-
  Kepler.Text.TameSpine.Reduction3QcdvkeaV0 — QCDVKEA i=0 槽形实例（chain 载体）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ QCDVKEA.hl:64-157 `QCDVKEA`（i := 0 实例）：
  │   ¬final_list L (rtrans L N r x 1) ∧ marked_list L N r x ∧
  │   find_face L x = f ∧ next_el f x = w ⇒
  │   indexf w (ztrans L N r x 0) f ≤ indexf w (ytrans L N r x 1) f
  │ （ztrans 0 = l'z L N r x、ytrans 1 = l'y L (rtrans 1) x，定义级 rfl）。
  │ 证体三段（HOL 同构）：
  │ ① y-index 锚（Pplhulj.hl:114 `indexf_ytrans_eq_l_m` 的 face-index 形，
  │    状态泛型）：indexf w (l'y L r x) f = l'm L r x；
  │    内含界支 l'm < sizel f（HOL :140 起 l'm ≥ sizel f 反证支，
  │    `qLmLtFace`：|f|-周期位移把 P(l'm) 拉回 P(l'm − |f|) 撞极小性）；
  │ ② min_num_le（qcdvkea.hl:32）= 树内 `minNumLE`；非空支（HOL :124-150
  │    逆否）= `qDepartNonempty`（{P}=∅ ⇒ final_list）；
  │ ③ 三角割支（HOL :94-120）：i < indexf w z f ⇒ NCVIBWU 于 i、i+1 两次
  │    （`ncvibwuV0FullChain`）+ indexf_n ⇒ 状态 1 的 l'm 谓词在 i 处不成立。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS ─────────────────────────────────────────────────────
  │ ① 前提：HOL 的 `¬final_list L (rtrans … (SUC i))` 于 i=0 逐字保留为
  │    `hf1`（候选形漏写；缺之则 {P} 可空、l'm 取 junk 值、陈述不可证）；
  │    状态 0 的 ¬final 由 `finalListInduct` 一步导出。
  │ ② 状态 1 的全部载体事实走 chain `markedList` 合取（AqiunppSlot 一步），
  │    不经 spine（免状态 1 的 sList 槽）；状态 0 侧 `hs` 槽逐字保留
  │    （仅 `ncvibwuV0FullChain` 消费）。
  │ ③ 锚的吻合段不调链版 `minNotEqImpEq`（其集合表示为 f (f (f^[m] x)) 形，
  │    与 `lm` 定义集不同构），改由 `minNum_spec` 极小性直接归纳（`qAgree`）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓双零写入；既有文件零触碰。
-/

import Kepler.Text.TameSpine.Reduction3NcvibwuIndexMain
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Aux
import Kepler.Text.Reduction5Qcdvkea

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup dart_in_face nextEl_mem_of_mem
  getElem_idxOf getD_eq_getElem_of_lt nextEl_eq_getD)
open Kepler.Text.Reduction5 (Dart finalList lm ly lz rtrans ntrans minNum minNum_spec)

/-! ## §1 轨道与周期件 -/

/-- nextEl 幂保成员（B2b 私件同款重推导）。 -/
private theorem qOrbitMem {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    {a : α} (ha : a ∈ s) : ∀ k : ℕ, (nextEl s)^[k] a ∈ s := by
  intro k
  induction k with
  | zero => exact ha
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- `(m % len + 1) % len = (m + 1) % len`（B2d 私件同款重推导）。 -/
private theorem qModSucc (m len : ℕ) : (m % len + 1) % len = (m + 1) % len := by
  have h : m + 1 = len * (m / len) + (m % len + 1) := by
    have := Nat.div_add_mod m len
    omega
  rw [h, Nat.add_comm (len * (m / len)), Nat.add_mul_mod_self_left]

/-- 轨道枚举：`(nextEl s)^[k] a = s.getD ((s.idxOf a + k) % |s|) a`
（B2d 私件同款重推导）。 -/
private theorem qOrbitGet {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) (hpos : 0 < s.length) {a : α} (ha : a ∈ s) (k : ℕ) :
    (nextEl s)^[k] a = s.getD ((s.idxOf a + k) % s.length) a := by
  have hilt : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr ha
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.add_zero, Nat.mod_eq_of_lt hilt,
      getD_eq_getElem_of_lt hilt, getElem_idxOf ha]
  | succ k ih =>
    have hdmem : s.getD ((s.idxOf a + k) % s.length) a ∈ s := by
      have hm : (s.idxOf a + k) % s.length < s.length := Nat.mod_lt _ hpos
      rw [getD_eq_getElem_of_lt hm]
      exact List.getElem_mem hm
    have hidxm : s.idxOf (s.getD ((s.idxOf a + k) % s.length) a)
        = (s.idxOf a + k) % s.length := by
      rw [getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
      exact hnd.idxOf_getElem ((s.idxOf a + k) % s.length) (Nat.mod_lt _ hpos)
    rw [Function.iterate_succ_apply', ih, nextEl_eq_getD hdmem, hidxm, qModSucc,
      show s.idxOf a + k + 1 = s.idxOf a + (k + 1) from by omega,
      getD_eq_getElem_of_lt (Nat.mod_lt _ hpos),
      getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

/-- 周期位移：`(nextEl s)^[k + |s|] a = (nextEl s)^[k] a`。 -/
private theorem qOrbitPeriod {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) {a : α} (ha : a ∈ s) (k : ℕ) :
    (nextEl s)^[k + s.length] a = (nextEl s)^[k] a := by
  have hpos : 0 < s.length := List.length_pos_of_mem ha
  rw [qOrbitGet hnd hpos ha (k + s.length), qOrbitGet hnd hpos ha k,
    show s.idxOf a + (k + s.length) = s.idxOf a + k + s.length from by omega,
    Nat.add_mod_right]

/-- 周期位移（减法形，k ≥ |s|）。 -/
private theorem qOrbitPeriodSub {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} (hnd : s.Nodup) {a : α} (ha : a ∈ s) {k : ℕ} (hk : s.length ≤ k) :
    (nextEl s)^[k] a = (nextEl s)^[k - s.length] a := by
  have h := qOrbitPeriod hnd ha (k - s.length)
  rw [Nat.sub_add_cancel hk] at h
  exact h

/-! ## §2 l'm 谓词：非空支与界支 -/

/-- 非空支（QCDVKEA.hl:124-150 逆否）：`¬final_list L r ⇒ {m | P m} ≠ ∅`
（P m := l'm 谓词）。{P}=∅ 时 `indexf_n` 把 r 的任一元写成 x 的 nextEl 幂，
逐点得 `f_list L d = next_el r d`，即 final。 -/
private theorem qDepartNonempty {L : fgraph ℕ} {r : List Dart} {x : Dart}
    (hx1 : x ∈ r) (hrnd : r.Nodup) (hnext : nextEl r x = fList L x)
    (hf : ¬ finalList L r) :
    ({m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)} : Set ℕ).Nonempty := by
  by_contra hempty
  apply hf
  intro d hd
  have hfx : fList L x ∈ r := by
    rw [← hnext]; exact nextEl_mem_of_mem hx1
  have hidx := indexfN hfx hd hrnd
  -- hidx : (nextEl r)^[indexf (fList L x) d r] (fList L x) = d
  have hall : (nextEl r)^[indexf (fList L x) d r + 2] x
      = fList L ((nextEl r)^[indexf (fList L x) d r + 1] x) := by
    by_contra hbad
    exact hempty ⟨indexf (fList L x) d r, hbad⟩
  have hA : (nextEl r)^[indexf (fList L x) d r + 1] x = d := by
    rw [Function.iterate_succ_apply (nextEl r) (indexf (fList L x) d r) x, hnext]
    exact hidx
  have hB : (nextEl r)^[indexf (fList L x) d r + 2] x = nextEl r d := by
    have s : (nextEl r)^[indexf (fList L x) d r + 2] x
        = nextEl r ((nextEl r)^[indexf (fList L x) d r + 1] x) :=
      Function.iterate_succ_apply' (nextEl r) (indexf (fList L x) d r + 1) x
    rw [s, hA]
  rw [hA, hB] at hall
  exact hall.symm

/-- 界支（Pplhulj.hl:114 证体的 l'm ≥ sizel f 反证支）：`¬final_list L r ⇒
l'm L r x < |find_face L x|`。反设 l'm ≥ |f|：极小性给 j ≤ l'm+1 的轨道吻合
`(next_el r)^j x = (f_list L)^j x`，face 轨道 |f|-周期位移把 P(l'm) 拉回
P(l'm − |f|)，与 l'm 极小性矛盾。 -/
private theorem qLmLtFace (L : fgraph ℕ) (hL : GoodList L) {r : List Dart} {x : Dart}
    (hxd : x ∈ listOfDarts L) (hx1 : x ∈ r) (hrnd : r.Nodup)
    (hnext : nextEl r x = fList L x) (hf : ¬ finalList L r) :
    lm L r x < (findFaceDarts L x).length := by
  have hxb : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hne := qDepartNonempty hx1 hrnd hnext hf
  have hspec := minNum_spec hne
  have hPlm : (nextEl r)^[lm L r x + 2] x ≠ fList L ((nextEl r)^[lm L r x + 1] x) :=
    hspec.1
  -- 吻合：j ≤ l'm + 1 ⇒ (next_el r)^j x = (f_list L)^j x
  have hagree : ∀ j : ℕ, j ≤ lm L r x + 1 → (nextEl r)^[j] x = (fList L)^[j] x := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ k ih =>
      intro hj
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0]
        exact hnext
      · have hk2 : k - 1 + 2 = k + 1 := by omega
        have hk3 : k - 1 + 1 = k := by omega
        have hnd : ¬ ((nextEl r)^[k - 1 + 2] x ≠ fList L ((nextEl r)^[k - 1 + 1] x)) := by
          intro hbad
          have hle : lm L r x ≤ k - 1 := hspec.2 (k - 1) hbad
          omega
        rw [hk2, hk3] at hnd
        have hrec : (nextEl r)^[k + 1] x = fList L ((nextEl r)^[k] x) := not_not.mp hnd
        rw [hrec, ih (by omega)]
        exact (Function.iterate_succ_apply' (fList L) k x).symm
  by_contra hge
  have hlen : (findFaceDarts L x).length ≤ lm L r x := by omega
  have hflen : 0 < (findFaceDarts L x).length := List.length_pos_of_mem hxb
  -- 位移：o_{l'm+1} = o_{l'm+1−|f|}
  have hshift : (nextEl r)^[lm L r x + 1] x
      = (nextEl r)^[lm L r x + 1 - (findFaceDarts L x).length] x := by
    have h1 : (nextEl r)^[lm L r x + 1] x
        = (nextEl (findFaceDarts L x))^[lm L r x + 1 - (findFaceDarts L x).length] x := by
      rw [hagree _ (Nat.le_refl _), fListPowEqNextElPow L hL x hxb,
        qOrbitPeriodSub hfnd hxb (by omega)]
    rw [h1, ← fListPowEqNextElPow L hL x hxb, hagree _ (by omega)]
  have hI1 : lm L r x + 1 - (findFaceDarts L x).length
      = lm L r x - (findFaceDarts L x).length + 1 := by omega
  have hstep2 : (nextEl r)^[lm L r x + 2] x
      = (nextEl r)^[lm L r x - (findFaceDarts L x).length + 2] x := by
    have s : (nextEl r)^[lm L r x + 2] x = nextEl r ((nextEl r)^[lm L r x + 1] x) :=
      Function.iterate_succ_apply' (nextEl r) (lm L r x + 1) x
    have s2 : nextEl r ((nextEl r)^[lm L r x + 1 - (findFaceDarts L x).length] x)
        = (nextEl r)^[lm L r x + 1 - (findFaceDarts L x).length + 1] x :=
      (Function.iterate_succ_apply' (nextEl r)
        (lm L r x + 1 - (findFaceDarts L x).length) x).symm
    rw [s, hshift, s2, hI1]
  have hR : fList L ((nextEl r)^[lm L r x + 1] x)
      = fList L ((nextEl r)^[lm L r x - (findFaceDarts L x).length + 1] x) := by
    rw [hshift, hI1]
  rw [hstep2, hR] at hPlm
  have hle : lm L r x ≤ lm L r x - (findFaceDarts L x).length := hspec.2 _ hPlm
  omega

/-! ## §3 y-index 锚（Pplhulj.hl:114 的 face-index 形，状态泛型） -/

/-- **HOL `Pplhulj.indexf_ytrans_eq_l_m`**（face-index 形，状态泛型）：
`indexf w (l'y L r x) f = l'm L r x`（w = next_el f x、f = find_face L x）。 -/
private theorem qAnchorFIdx (L : fgraph ℕ) (hL : GoodList L) {r : List Dart} {x : Dart}
    (hxd : x ∈ listOfDarts L) (hx1 : x ∈ r) (hrnd : r.Nodup)
    (hnext : nextEl r x = fList L x) (hf : ¬ finalList L r)
    {f : List Dart} (hfind : findFaceDarts L x = f) {w : Dart}
    (hw : nextEl f x = w) :
    indexf w (Kepler.Text.Reduction5.ly L r x) f = lm L r x := by
  have hxb : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hxf : x ∈ f := by rw [← hfind]; exact hxb
  have hwf : w ∈ f := by rw [← hw]; exact nextEl_mem_of_mem hxf
  have hfnd : f.Nodup := by rw [← hfind]; exact findFaceDarts_nodup hL.1 x
  have hfpow : ∀ k : ℕ, (fList L)^[k] x = (nextEl f)^[k] x := by
    intro k
    rw [fListPowEqNextElPow L hL x hxb, hfind]
  have hlyW : (nextEl f)^[lm L r x] w = Kepler.Text.Reduction5.ly L r x := by
    have hd : Kepler.Text.Reduction5.ly L r x = (fList L)^[lm L r x + 1] x := rfl
    rw [hd, hfpow, ← hw]
    exact (Function.iterate_succ_apply (nextEl f) (lm L r x) x).symm
  have hlym : Kepler.Text.Reduction5.ly L r x ∈ f := by
    rw [← hlyW]
    exact qOrbitMem hwf _
  have hbl : lm L r x < f.length := by
    rw [← hfind]
    exact qLmLtFace L hL hxd hx1 hrnd hnext hf
  exact nextElnIndexf hwf hlym hfnd hlyW hbl

/-! ## §4 QCDVKEA i=0 -/

/-- **HOL `QCDVKEA`**（QCDVKEA.hl:64-157，i := 0 实例，chain 载体）：
`¬final_list L (rtrans L N r x 1) ∧ marked_list L N r x ∧ find_face L x = f ∧
next_el f x = w ⇒ indexf w (l'z L N r x) f ≤ indexf w (l'y L (rtrans L N r x 1) x) f`。
`transform_assumption_v2` ↦ `AqiunppSlot`；`hs` 为状态 0 的生态槽
（仅 `ncvibwuV0FullChain` 消费）。 -/
theorem qcdvkeaV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hs : Kepler.Text.ChainLists.sList L r x = sListSpine L r x)
    (hf1 : ¬ finalList L (rtrans L N r x 1))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) :
    indexf w (lz L N r x) f ≤ indexf w (Kepler.Text.Reduction5.ly L (rtrans L N r x 1) x) f := by
  -- 状态 1 载体（AqiunppSlot 一步）
  have hm1 := haq hgn N r x hm 1
  have hrnd1 : (rtrans L N r x 1).Nodup :=
    (List.nodup_flatten.mp hm1.2.1.1).1 (rtrans L N r x 1) hm1.2.2.1
  have hx1 : x ∈ rtrans L N r x 1 := hm1.2.2.2.1
  have hnext1 : nextEl (rtrans L N r x 1) x = fList L x := hm1.2.2.2.2.2.1
  have hf0 : ¬ finalList L r := Kepler.Text.Reduction5.finalListInduct 0 hf1
  have hxd : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hxb : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hfpow : ∀ k : ℕ, (fList L)^[k] x = (nextEl f)^[k] x := by
    intro k
    rw [fListPowEqNextElPow L hL x hxb, hfind]
  have hw1 : nextEl (rtrans L N r x 1) x = w := by
    rw [hnext1]
    show nextEl (findFaceDarts L x) x = w
    rw [hfind]; exact hw
  have hwmem1 : w ∈ rtrans L N r x 1 := by
    rw [← hw1]; exact nextEl_mem_of_mem hx1
  -- ① y-index 锚
  rw [qAnchorFIdx L hL hxd hx1 hrnd1 hnext1 hf1 hfind hw]
  -- ② min_num_le：非空支 + 三角割支
  refine Kepler.Text.MoreLemma2Aux.minNumLE
    (P := fun k => (nextEl (rtrans L N r x 1))^[k + 2] x
      ≠ fList L ((nextEl (rtrans L N r x 1))^[k + 1] x))
    rfl ?_ (qDepartNonempty hx1 hrnd1 hnext1 hf1)
  -- ③ 三角割支：i < indexf w z f ⇒ NCVIBWU 于 i、i+1 ⇒ 谓词在 i 处不成立
  intro i hiZ
  obtain ⟨hmemI, hidxI⟩ := ncvibwuV0FullChain L hL hgn hunL haq hm hs hf0 hfind hw
    (j := i) (by omega)
  obtain ⟨hmemS, hidxS⟩ := ncvibwuV0FullChain L hL hgn hunL haq hm hs hf0 hfind hw
    (j := i + 1) (by omega)
  have hI0 : (nextEl (rtrans L N r x 1))^[i] w = (nextEl f)^[i] w := by
    have h1 := indexfN hwmem1 hmemI hrnd1
    rw [hidxI] at h1
    exact h1
  have hI1 : (nextEl (rtrans L N r x 1))^[i + 1] w = (nextEl f)^[i + 1] w := by
    have h1 := indexfN hwmem1 hmemS hrnd1
    rw [hidxS] at h1
    exact h1
  have hmid : (nextEl (rtrans L N r x 1))^[i + 1] x = (nextEl f)^[i] w := by
    rw [Function.iterate_succ_apply (nextEl (rtrans L N r x 1)) i x, hw1, hI0]
  have s1 : (nextEl (rtrans L N r x 1))^[i + 2] x
      = (nextEl (rtrans L N r x 1))^[i + 1] w := by
    have s : (nextEl (rtrans L N r x 1))^[i + 2] x
        = (nextEl (rtrans L N r x 1))^[i + 1] (nextEl (rtrans L N r x 1) x) :=
      Function.iterate_succ_apply (nextEl (rtrans L N r x 1)) (i + 1) x
    rw [s, hw1]
  have hfl : (nextEl f)^[i] w = (fList L)^[i + 1] x := by
    rw [← hw, ← Function.iterate_succ_apply (nextEl f) i x, ← hfpow]
  have e : (nextEl (rtrans L N r x 1))^[i + 2] x
      = fList L ((nextEl (rtrans L N r x 1))^[i + 1] x) := by
    rw [s1, hI1, hmid, hfl, ← Function.iterate_succ_apply' (fList L) (i + 1) x,
      hfpow, ← hw]
    exact (Function.iterate_succ_apply (nextEl f) (i + 1) x).symm
  intro hbad
  exact hbad e

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.TameSpine.qcdvkeaV0
#print axioms Kepler.Text.TameSpine.qDepartNonempty
#print axioms Kepler.Text.TameSpine.qLmLtFace
#print axioms Kepler.Text.TameSpine.qAnchorFIdx
#print axioms Kepler.Text.TameSpine.qOrbitGet
#print axioms Kepler.Text.TameSpine.qOrbitPeriod
