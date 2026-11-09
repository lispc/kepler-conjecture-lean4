/-
  Kepler.Text.MoreLemma2QuotientAlt2 — J 战役 J1（M0h3）：
  `f_list_quotient_alt` 收尾片（next_el_flatten_last 族 + next_el_parts_last + 装配）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/tame_list.hl`）──
  │ 公开件：
  │   :5803  `next_el_flatten_last`      → nextElFlattenLast
  │   :6505  `next_el_parts_last`        → nextElPartsLast
  │   :7976  `f_list_quotient_alt`       → fListQuotientAlt
  │ 私有机器：nextEl_last!（末元回卷）、idxOfGetLast、nextEl_cat_last!（:5683
  │   族）、head!_flatten_cons、flatten_ne_nil。
  └────────────────────────────────────────────────────────────────

  ┌─ 实现要点（Spine 对照）───────────────────────────────────────
  │ `nextElFlattenLast`：`List.append_of_mem` 把 r 拆成 a ++ r :: b；
  │ b = [] 支两侧都回卷到首元（`nextEl_last!`），b ≠ [] 支
  │ LHS 走 `nextEl_cat_last!`（b.flatten 首元）、RHS 走 atom 表
  │ idxOf/getD 表达（`b.head!`），以 `head!_flatten_cons` 收口。
  │ `r ∉ a` 由 flatten Nodup 的 `nodup_append` Disjoint 直接反证
  │ （免去 Spine 的 nodupOfFlattenNodup 机）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；Dart 具体载体。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.ChainListsL1
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2QuotientAlt

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2QuotientAlt2

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart parts)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.MoreLemma2Island2 (partsFlatten partsAllNonnil partsNonnil)
open Kepler.Text.MoreLemma2Island3 (partsUniqNonnil)
open Kepler.Text.MoreLemma2Naming (uniqSublistUnique)
open Kepler.Text.MoreLemma2QuotientAlt (normalListPartsNextLast)
open Kepler.Assembly (fList eList nextEl GoodList)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt getElem_idxOf
  idxOf_getElem nextEl_mem_of_mem)

/-- 形状 wrapper：`List.flatten_append` 的实参名是 L₁/L₂，这里钉死调用形。 -/
private theorem flatten_append_shape {α : Type*} {a b : List (List α)} :
    (a ++ b).flatten = a.flatten ++ b.flatten :=
  List.flatten_append

/-- 形状 wrapper：`getElem_append_right` 的 `h₂` 是隐式的，这里钉死
`i = as.length` 的调用形（dependent index/证明由 wrapper 承担）。
`hb`（`bs` 非空）是右端 `bs[0]` 与左端界所需的唯一前提；`h` 显式承接
调用点的界项，使 `rw` 的证明项按语法命中。 -/
private theorem getElem_append_right_len {α : Type*} (as bs : List α)
    (hb : 0 < bs.length) (h : as.length < (as ++ bs).length) :
    (as ++ bs)[as.length]'h = bs[0]'(by omega) := by
  have h₁ : as.length ≤ as.length := Nat.le_refl _
  rw [List.getElem_append_right (as := as) (bs := bs) (i := as.length) h₁ (h₂ := h)]
  simp only [Nat.sub_self]

/-- 形状 wrapper：`(as ++ y :: bs)[as.length + 1] = bs[0]`（`hb : 0 < bs.length`）。
`y :: bs` 的第 0 个元素是取右段首元的固定形；`h` 显式承接调用点界项。 -/
private theorem getElem_append_cons_right {α : Type*} (as bs : List α) (y : α)
    (hb : 0 < bs.length) (h : as.length + 1 < (as ++ y :: bs).length) :
    (as ++ y :: bs)[as.length + 1]'h = bs[0]'(by omega) := by
  have h₁ : as.length ≤ as.length + 1 := by omega
  have key := List.getElem_append_right (as := as) (bs := y :: bs) (i := as.length + 1) h₁ (h₂ := h)
  rw [key]
  simp only [show as.length + 1 - as.length = 1 from by omega]
  cases bs with
  | nil => exact absurd hb (by simp)
  | cons b0 bs' => rfl

/-- `l[0] = l.head!`（`l` 非空；`cases l` 即 rfl）。 -/
private theorem getElem_zero_head! {α : Type*} [Inhabited α] {l : List α} (h : 0 < l.length) :
    l[0]'h = l.head! := by
  cases l with
  | nil => simp at h
  | cons a t => rfl

/-! ## §1 末元 machinery（私件；补 QuotientAlt 私有区的 getLast! 族） -/

/-- 非空表 `getLast!` 成员。 -/
private theorem getLastMem {l : List Dart} (h : l ≠ []) : l.getLast! ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- `l[len-1]` 与 `getLast!` 项级换形。 -/
private theorem getElemLastGetLast! {l : List Dart} (hpos : 0 < l.length) :
    l[l.length - 1]'(by omega) = l.getLast! := by
  have h1 : (l[l.length - 1]? : Option Dart).getD default = l[l.length - 1]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, h1]

/-- `indexl (getLast!) = len - 1`（Nodup）。 -/
private theorem idxOfGetLast! {s : List Dart} (hun : s.Nodup) (hne : s ≠ []) :
    s.idxOf s.getLast! = s.length - 1 := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  have hmem : s.getLast! ∈ s := getLastMem hne
  rw [← getElemLastGetLast! hpos]
  exact idxOf_getElem hun (by omega)

/-- 末元回卷：`nextEl s (s.getLast!) = s.head!`（Nodup）。 -/
private theorem nextEl_last! {s : List Dart} (hun : s.Nodup) (hne : s ≠ []) :
    nextEl s s.getLast! = s.head! := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hne
  have hmem : s.getLast! ∈ s := getLastMem hne
  rw [nextEl_eq_getD hmem, idxOfGetLast! hun hne,
    show s.length - 1 + 1 = s.length from by omega, Nat.mod_self,
    getD_eq_getElem_of_lt hpos]
  cases s with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- 拼接表末元缺省件：`(s ++ t).getLast! = t.getLast!`（t 非空）。 -/
private theorem lastCat {s t : List Dart} (ht : t ≠ []) :
    (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_append_of_ne_nil _ ht,
    List.getLast!_eq_getLast?_getD]

/-- **HOL `next_el_cat_last1`**（tame_list.hl:5683）
`uniq (s ++ t) ∧ s ≠ [] ∧ t ≠ [] ==> next_el (s ++ t) (LAST s) = HD t`。 -/
private theorem nextEl_cat_last! {s t : List Dart} (hnd : (s ++ t).Nodup)
    (hs : s ≠ []) (ht : t ≠ []) :
    nextEl (s ++ t) s.getLast! = t.head! := by
  have hsn : s.Nodup := (List.nodup_append.mp hnd).1
  have hpos : 0 < s.length := List.length_pos_of_ne_nil hs
  have htl : 0 < t.length := List.length_pos_of_ne_nil ht
  have hmem : s.getLast! ∈ s := getLastMem hs
  have hidx : (s ++ t).idxOf s.getLast! = s.length - 1 := by
    rw [List.idxOf_append_of_mem hmem, idxOfGetLast! hsn hs]
  have hmod : (s.length - 1 + 1) % (s ++ t).length = s.length % (s ++ t).length := by
    rw [show s.length - 1 + 1 = s.length from by omega]
  have hbound : s.length < (s ++ t).length := by
    rw [List.length_append]; exact Nat.lt_add_of_pos_right htl
  rw [nextEl_eq_getD (List.mem_append.mpr (Or.inl hmem)), hidx, hmod,
    Nat.mod_eq_of_lt hbound, getD_eq_getElem_of_lt hbound]
  rw [getElem_append_right_len s t (List.length_pos_of_ne_nil ht) hbound]
  cases t with
  | nil => exact absurd rfl ht
  | cons b t' => rfl

/-- flatten 首元 = 首 atom 首元（单 cons 形）。 -/
private theorem head!_flatten_cons {u : List Dart} {t : List (List Dart)} (hu : u ≠ []) :
    (u :: t).flatten.head! = u.head! := by
  rw [List.flatten_cons]
  cases u with
  | nil => exact absurd rfl hu
  | cons a u' => rfl

/-- 全非空表的 flatten 非空。 -/
private theorem flatten_ne_nil {L : List (List Dart)} (hn : ∀ q ∈ L, q ≠ []) (hL : L ≠ []) :
    L.flatten ≠ [] := by
  cases L with
  | nil => exact absurd rfl hL
  | cons u t =>
    rw [List.flatten_cons]
    intro hc
    have hu : u = [] := by
      cases u with
      | nil => rfl
      | cons a u' => rw [List.cons_append] at hc; exact absurd hc (by simp)
    exact hn u (List.mem_cons_self ..) hu

/-- `(a ++ [r]).length = a.length + 1`（三处 length 算术的固定形）。
**多态**：`b = []` 支里 `a : List (List Dart)`、`r : List Dart`（原子层），
单态 `List Dart` 版在该支不可用（这是 M0h3c 三处 error 的真根因）。 -/
private theorem length_app_singleton {α : Type*} (a : List α) (r : α) :
    (a ++ [r]).length = a.length + 1 := by
  rw [List.length_append]
  rfl

/-! ## §2 next_el_flatten_last（:5803） -/

/-- **HOL `next_el_flatten_last`**（tame_list.hl:5803
`uniq (flatten L) /\ all (\q. ~(q = [])) L /\ MEM r L ==>
  next_el (flatten L) (LAST r) = HD (next_el L r)`）。
Spine 现名 `nextElFlattenLast`（TameList9:1137）。 -/
theorem nextElFlattenLast {L : List (List Dart)} {r : List Dart}
    (hun : L.flatten.Nodup) (hn : ∀ q ∈ L, q ≠ []) (hr : r ∈ L) :
    nextEl L.flatten r.getLast! = (nextEl L r).head! := by
  have hr0 : r ≠ [] := hn r hr
  obtain ⟨a, b, hab⟩ := List.append_of_mem hr
  rw [hab] at hun ⊢
  have hfl1 : ((a ++ r :: b)).flatten = (a.flatten ++ r) ++ b.flatten := by
    rw [flatten_append_shape, List.flatten_cons, List.append_assoc]
  have hSfl : ((a.flatten ++ r) ++ b.flatten).Nodup := hfl1 ▸ hun
  have hra : r ∉ a := by
    intro hc
    have hnd : (a.flatten ++ (r :: b).flatten).Nodup := by
      rw [← flatten_append_shape]; exact hun
    have hx1 : r.head! ∈ a.flatten := List.mem_flatten.mpr ⟨r, hc, List.head!_mem_self hr0⟩
    have hx2 : r.head! ∈ (r :: b).flatten :=
      List.mem_flatten.mpr ⟨r, List.mem_cons_self .., List.head!_mem_self hr0⟩
    exact (List.nodup_append.mp hnd).2.2 _ hx1 _ hx2 rfl
  have hSne : a.flatten ++ r ≠ [] :=
    List.ne_nil_of_mem (List.mem_append.mpr (Or.inr (getLastMem hr0)))
  have hSn : (a.flatten ++ r).Nodup :=
    List.Sublist.nodup (List.sublist_append_left _ b.flatten) hSfl
  have hlast : r.getLast! = (a.flatten ++ r).getLast! := (lastCat hr0).symm
  by_cases hb0 : b = []
  · -- b = []：两侧独立 have 收口到同一头元
    subst hb0
    have hflat : ((a ++ r :: ([] : List (List Dart)))).flatten = a.flatten ++ r := by
      rw [flatten_append_shape, List.flatten_cons, List.flatten_nil, List.append_nil]
    have hLHS : nextEl ((a ++ r :: ([] : List (List Dart)))).flatten r.getLast!
        = (a.flatten ++ r).head! := by
      rw [hflat, hlast]
      exact nextEl_last! hSn hSne
    have hRHS : (nextEl (a ++ r :: ([] : List (List Dart))) r).head!
        = (a.flatten ++ r).head! := by
      have hidx : (a ++ [r]).idxOf r = (a ++ [r]).length - 1 := by
        have hidx2 : (a ++ [r]).idxOf r = a.length := by
          rw [List.idxOf_append_of_notMem hra, List.idxOf_cons_self, Nat.add_zero]
        rw [hidx2, length_app_singleton]
        omega
      have hwrap : nextEl (a ++ [r]) r = (a ++ [r]).head! := by
        have hmem' : r ∈ a ++ [r] := List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
        rw [nextEl_eq_getD hmem', hidx,
          show (a ++ [r]).length - 1 + 1 = (a ++ [r]).length from by
            rw [length_app_singleton]; omega,
          Nat.mod_self, getD_eq_getElem_of_lt (by rw [length_app_singleton]; omega)]
        exact getElem_zero_head! (l := a ++ [r]) (by rw [length_app_singleton]; omega)
      rw [hwrap]
      cases a with
      | nil => rfl
      | cons c t =>
        cases c with
        | nil =>
          exact absurd rfl (hn [] (by rw [hab]; exact List.mem_cons_self ..))
        | cons a0 c' => rfl
    rw [hLHS, hRHS]
  · -- b ≠ []：LHS 走 cat_last，RHS 走 atom 表 getD
    have hbne : b ≠ [] := hb0
    -- 一次拆成 `q :: t`（避免 `subst` 后 `b` 形与 `[r]`/`r :: []` 混写）
    obtain ⟨q, t, rfl⟩ := List.exists_cons_of_ne_nil hbne
    have hbfl : (q :: t).flatten ≠ [] := flatten_ne_nil
      (fun s hs => hn s (by rw [hab]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hs))))
      (List.cons_ne_nil q t)

    have hLHS : nextEl ((a ++ r :: q :: t)).flatten r.getLast! = (q :: t).flatten.head! := by
      rw [hfl1, hlast]
      exact nextEl_cat_last! hSfl hSne hbfl
    have hRHS : (nextEl (a ++ r :: q :: t) r).head! = (q :: t).flatten.head! := by
      have hidx : (a ++ r :: q :: t).idxOf r = a.length := by
        rw [List.idxOf_append_of_notMem hra, List.idxOf_cons_self, Nat.add_zero]
      -- `omega` 需要显式正性：`(q :: t)` 非空 ⇒ 长度 ≥ 1
      have hbpos : 0 < (q :: t).length := List.length_pos_of_ne_nil (List.cons_ne_nil q t)
      have hlt : a.length + 1 < (a ++ r :: q :: t).length := by
        rw [List.length_append, List.length_cons]
        omega
      have hmem' : r ∈ a ++ r :: q :: t := List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
      have hnext : nextEl (a ++ r :: q :: t) r = (q :: t).head! := by
        rw [nextEl_eq_getD hmem', hidx, Nat.mod_eq_of_lt hlt, getD_eq_getElem_of_lt hlt,
          getElem_append_cons_right a (q :: t) r hbpos hlt]
        rfl
      rw [hnext]
      have hbrest : (q :: t).head! ∈ L := by
        rw [hab]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons_of_mem _ (List.head!_mem_self (List.cons_ne_nil q t))))
      have hbhne : (q :: t).head! ≠ [] := hn _ hbrest
      have hqne : q ≠ [] := by simpa using hbhne
      rw [List.flatten_cons, List.head!_append t.flatten hqne]
      rfl
    rw [hLHS, hRHS]

/-! ## §3 next_el_parts_last（:6505） -/

/-- **HOL `next_el_parts_last`**（tame_list.hl:6505
`uniq r ∧ ~(r = []) ∧ MEM x p ∧ MEM p (parts L r) ∧ x = LAST p ==>
  next_el r x = HD (next_el (parts L r) p)`）。
Spine 现名 `nextElPartsLast`（TameList9:1383）。 -/
theorem nextElPartsLast (L : fgraph ℕ) {r : List Dart} (hun : r.Nodup) (hne : r ≠ [])
    {p : List Dart} (hp : p ∈ parts L r) {x : Dart} (hx : x ∈ p) (hxl : x = p.getLast!) :
    nextEl r x = (nextEl (parts L r) p).head! := by
  have hpfl : (parts L r).flatten.Nodup := by
    rw [partsFlatten L hun hne]; exact hun
  have hpn : ∀ q ∈ parts L r, q ≠ [] := partsAllNonnil L r
  conv_lhs => rw [← partsFlatten L hun hne]
  rw [hxl]
  exact nextElFlattenLast hpfl hpn hp

/-! ## §4 f_list_quotient_alt（:7976） -/

/-- **HOL `f_list_quotient_alt`**（tame_list.hl:7976
`normal_list L N ∧ MEM p (parts L r) ∧ MEM p' (parts L r') ∧ MEM r N ∧ MEM r' N ==>
  (next_el (parts L r) p = p' <=> MEM (f_list L (LAST p)) p')`）。
Spine 现名 `fListQuotientAlt`（TameList11:424）。
链岛证体：hkey = normalListPartsNextLast.symm.trans nextElPartsLast；
正向 head! 成员、反向 uniqSublistUnique 双发。 -/
theorem fListQuotientAlt (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) {r r' : List Dart} (hr : r ∈ N) (hr' : r' ∈ N)
    {p p' : List Dart} (hp : p ∈ parts L r) (hp' : p' ∈ parts L r') :
    (nextEl (parts L r) p = p' ↔ fList L (p.getLast!) ∈ p') := by
  have hrN : r.Nodup := (List.nodup_flatten.mp hN.1).1 r hr
  have hrne : r ≠ [] := hN.2.1 r hr
  have hr'N : r'.Nodup := (List.nodup_flatten.mp hN.1).1 r' hr'
  have hr'ne : r' ≠ [] := hN.2.1 r' hr'
  have hpne : p ≠ [] := partsAllNonnil L r p hp
  have hpne' : p' ≠ [] := partsAllNonnil L r' p' hp'
  have hkey : fList L (p.getLast!) = (nextEl (parts L r) p).head! :=
    (normalListPartsNextLast L hL hN hr hp).symm.trans
      (nextElPartsLast L hrN hrne hp (getLastMem hpne) rfl)
  constructor
  · intro h
    rw [hkey, h]
    exact List.head!_mem_self hpne'
  · intro hcon
    rw [hkey] at hcon
    have hw : nextEl (parts L r) p ∈ parts L r := nextEl_mem_of_mem hp
    have hhd : (nextEl (parts L r) p).head! ∈ nextEl (parts L r) p :=
      List.head!_mem_self (partsAllNonnil L r _ hw)
    have hfinR : (nextEl (parts L r) p).head! ∈ r :=
      (partsUniqNonnil L hL hN hr hw).2.2.2.2 _ hhd
    have hfinP : (nextEl (parts L r) p).head! ∈ r' :=
      (partsUniqNonnil L hL hN hr' hp').2.2.2.2 _ hcon
    have hrr : r = r' :=
      uniqSublistUnique N hN.1 r hr r' hr' ⟨_, hfinR, hfinP⟩
    subst hrr
    exact uniqSublistUnique (parts L r) (by rw [partsFlatten L hrN hrne]; exact hrN)
      _ hw p' hp' ⟨_, hhd, hcon⟩

end Kepler.Text.MoreLemma2QuotientAlt2

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2QuotientAlt2.nextElFlattenLast
#print axioms Kepler.Text.MoreLemma2QuotientAlt2.nextElPartsLast
#print axioms Kepler.Text.MoreLemma2QuotientAlt2.fListQuotientAlt
