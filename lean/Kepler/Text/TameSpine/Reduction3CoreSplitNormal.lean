/-
  Kepler.Text.TameSpine.Reduction3CoreSplitNormal — 件 8a：core_split_normal_list
  主机（More_lemma1.hl:2028-3082）上游缺件层。Spine 侧文件（可 import 链 def；链侧禁
  import Spine）。

  ┌─ 归属对账（HOL Light Flyspeck）────────────────────────────────
  │ tame_list.hl:13285   `hd_cat`             → hdCat
  │ Seq2-compiled.hl:1894 `next_el_inj`        → nextElInj（链侧缺私件先例：
  │   TameList10:162 private 同体，本件公开泛型化）
  │ more_lemma1.hl:1528  `MEM_HD_LAST_betwn`  → memHdLastBetwn
  │ more_lemma1.hl:1550  `LAST_HD_LAST_betwn` → lastHdLastBetwn
  │ more_lemma1.hl:1559  `next_HD_LAST_betwn` → nextHdLastBetwn
  │ more_lemma1.hl:1618  `eq_HD_LAST_betwn`   → eqHdLastBetwn
  │ reduction4.hl:1509   `HD_flatten`         → 复用链现成件
  │   `Kepler.Text.Reduction4Idx.HD_flatten`（Reduction4Subseg3:63，泛型，不重落）
  │ 本簇路线（对表 §4 简化）：**直接证 `eqHdLastBetwn`**（`between` 取头→尾整段 =
  │ `tl.dropLast`），MEM/LAST/next 三件成为一行推论；HOL 的
  │ `betwn_cases`/`next_el_last_hd`/`betwn_nil` 路线不再需要。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；本节零 parts 依赖。
-/

import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.TameLp
import Kepler.Text.Reduction4
import Kepler.Text.Reduction4Subseg3
import Kepler.Text.TameSpine.TameList70
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (between)
open Kepler.Assembly (nextEl prevEl fList)
open Kepler.Text.Reduction5 (Dart finalList indexf)

/-! ## §1 `hd_cat`（tame_list.hl:13285） -/

/-- **HOL `Tame_list.hd_cat`**（tame_list.hl:13285）：`a ≠ [] ⇒ HD (a ++ b) = HD a`。 -/
theorem hdCat {α : Type*} [Inhabited α] {a b : List α} (ha : a ≠ []) :
    (a ++ b).head! = a.head! :=
  List.head!_append b ha

/-! ## §2 `next_el_inj`（Seq2-compiled.hl:1894；链侧缺，公开泛型化） -/

/-- `next_el` 对非成员恒等（junk 支；`uniq` 无关）。 -/
private theorem nextElOfNotMem {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hx : x ∉ s) : nextEl s x = x := by
  by_cases hnil : s = []
  · subst hnil
    simp [nextEl]
  · have hpos : 0 < s.length := List.length_pos_iff.mpr hnil
    have hidx : s.idxOf x = s.length := List.idxOf_eq_length hx
    unfold nextEl
    rw [hidx, if_neg (by omega)]
    exact List.getD_eq_default s x (by omega)

/-- **HOL `Seq2.next_el_inj`**（Seq2-compiled.hl:1894）：
`uniq s ⇒ (next_el s x = next_el s y ↔ x = y)`。 -/
theorem nextElInj {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} (hsn : s.Nodup) {x y : α} :
    nextEl s x = nextEl s y ↔ x = y := by
  constructor
  · intro h
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · have hpos : 0 < s.length := List.length_pos_of_mem hx
        have hxi : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
        have hyi : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
        rw [Kepler.Text.TameLp.nextEl_eq_getD hx,
          Kepler.Text.TameLp.nextEl_eq_getD hy] at h
        rw [Kepler.Text.TameLp.getD_eq_getElem_of_lt (Nat.mod_lt _ hpos),
          Kepler.Text.TameLp.getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)] at h
        have hidx : (s.idxOf x + 1) % s.length = (s.idxOf y + 1) % s.length :=
          Kepler.Text.TameLp.nodup_getElem_inj hsn _ _ h
        have hmod : ∀ a b n : ℕ, a < n → b < n →
            (a + 1) % n = (b + 1) % n → a = b := by
          intro a b n ha hb hab
          rcases Nat.eq_or_lt_of_le (show a + 1 ≤ n by omega) with ha2 | ha2
          · rcases Nat.eq_or_lt_of_le (show b + 1 ≤ n by omega) with hb2 | hb2
            · omega
            · rw [ha2, Nat.mod_self, Nat.mod_eq_of_lt hb2] at hab; omega
          · rcases Nat.eq_or_lt_of_le (show b + 1 ≤ n by omega) with hb2 | hb2
            · rw [hb2, Nat.mod_self, Nat.mod_eq_of_lt ha2] at hab; omega
            · rw [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at hab; omega
        exact (List.idxOf_inj hx).mp (hmod _ _ _ hxi hyi hidx)
      · rw [nextElOfNotMem hy] at h
        have hmem := Kepler.Text.TameLp.nextEl_mem_of_mem hx
        rw [h] at hmem
        exact absurd hmem hy
    · rw [nextElOfNotMem hx] at h
      by_cases hy : y ∈ s
      · have hmem := Kepler.Text.TameLp.nextEl_mem_of_mem hy
        rw [← h] at hmem
        exact absurd hmem hx
      · rw [nextElOfNotMem hy] at h
        exact h
  · intro h
    rw [h]

/-! ## §3 `eq_HD_LAST_betwn`（more_lemma1.hl:1618）+ MEM/LAST/next 三推论 -/

/-- `getLast!` 的 `getLast` 形（非空时；`getLast?` 路线）。 -/
private theorem getLastBangEqGetLast {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  rfl

/-- **HOL `Tame_list.eq_HD_LAST_betwn`**（more_lemma1.hl:1618）：
`¬(r=[]) ∧ uniq r ∧ ¬(HD r = LAST r) ⇒
r = [HD r] ++ (betwn r (HD r) (LAST r) ++ [LAST r])`。
链层直证：`r = hd :: tl`，`betwn r hd last = tl.dropLast`（`between_eq_take_of_idxOf_lt`
+ `dropLast_eq_take`），再 `dropLast_append_getLast` 拼回。 -/
theorem eqHdLastBetwn {α : Type*} [DecidableEq α] [Inhabited α] {r : List α}
    (hne : r ≠ []) (hnd : r.Nodup) (hne2 : r.head! ≠ r.getLast!) :
    r = [r.head!] ++ (between r r.head! r.getLast! ++ [r.getLast!]) := by
  cases r with
  | nil => exact absurd rfl hne
  | cons hd tl =>
    have htl : tl ≠ [] := by
      intro h
      refine hne2 ?_
      rw [h]
      simp [List.head!_cons, List.getLast!_eq_getLast?_getD]
    have hhead : (hd :: tl).head! = hd := List.head!_cons hd tl
    have hglProp : (hd :: tl).getLast! = (hd :: tl).getLast (by simp) := by
      rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast (by simp)]
      rfl
    have hlast : (hd :: tl).getLast! = tl.getLast htl := by
      rw [hglProp, List.getLast_cons htl]
    have hpos : 0 < (hd :: tl).length := by simp
    have hhdmem : hd ∈ hd :: tl := List.mem_cons_self
    have hlastmem : (hd :: tl).getLast! ∈ hd :: tl := by
      rw [hlast]; exact List.mem_cons_of_mem hd (List.getLast_mem htl)
    have hidxhd : (hd :: tl).idxOf hd = 0 := by
      have h := Kepler.Text.TameLp.idxOf_getElem (s := hd :: tl) hnd (i := 0) (by simp)
      exact h
    have hgl : (hd :: tl).getLast!
        = (hd :: tl)[(hd :: tl).length - 1]'(by simp) := by
      rw [hglProp]
      exact List.getLast_eq_getElem (by simp)
    have hidxlast : (hd :: tl).idxOf ((hd :: tl).getLast!)
        = (hd :: tl).length - 1 := by
      conv_lhs => rw [hgl]
      exact Kepler.Text.TameLp.idxOf_getElem (s := hd :: tl) hnd
        (i := (hd :: tl).length - 1) (by simp)
    have hbetween : between (hd :: tl) hd ((hd :: tl).getLast!) = tl.dropLast := by
      rw [Kepler.Text.Reduction4.between_eq_take_of_idxOf_lt hnd hhdmem hlastmem
        (by rw [hidxhd, hidxlast]; simpa using List.length_pos_iff.mpr htl)]
      rw [hidxhd, hidxlast]
      show List.take ((hd :: tl).length - 1 - 1) tl = tl.dropLast
      rw [show (hd :: tl).length - 1 - 1 = tl.length - 1 from by simp,
        List.dropLast_eq_take]
    rw [hhead, hbetween, hlast]
    rw [List.dropLast_append_getLast htl, List.singleton_append]

/-- **HOL `MEM_HD_LAST_betwn`**（more_lemma1.hl:1528）：
`¬(r=[]) ∧ uniq r ∧ ¬(HD r = LAST r) ⇒
(∀x, MEM x r ↔ MEM x (cat [HD r] (cat (betwn r (HD r) (LAST r)) [LAST r])))`。 -/
theorem memHdLastBetwn {α : Type*} [DecidableEq α] [Inhabited α] {r : List α}
    (hne : r ≠ []) (hnd : r.Nodup) (hne2 : r.head! ≠ r.getLast!) :
    ∀ x : α,
      x ∈ r ↔ x ∈ [r.head!] ++ (between r r.head! r.getLast! ++ [r.getLast!]) := by
  intro x
  constructor
  · intro hx
    rw [eqHdLastBetwn hne hnd hne2] at hx
    exact hx
  · intro hx
    rw [eqHdLastBetwn hne hnd hne2]
    exact hx

/-- **HOL `LAST_HD_LAST_betwn`**（more_lemma1.hl:1550）：
`¬(r=[]) ∧ uniq r ∧ ¬(HD r = LAST r) ⇒
LAST r = LAST (cat [HD r] (cat (betwn r (HD r) (LAST r)) [LAST r]))`（`getLast!` 形）。 -/
theorem lastHdLastBetwn {α : Type*} [DecidableEq α] [Inhabited α] {r : List α}
    (hne : r ≠ []) (hnd : r.Nodup) (hne2 : r.head! ≠ r.getLast!) :
    r.getLast!
      = ([r.head!] ++ (between r r.head! r.getLast! ++ [r.getLast!])).getLast! :=
  congrArg List.getLast! (eqHdLastBetwn hne hnd hne2)

/-- **HOL `next_HD_LAST_betwn`**（more_lemma1.hl:1559）：
`¬(r=[]) ∧ uniq r ∧ ¬(HD r = LAST r) ⇒
(∀x, MEM x r ⇒ next_el r x = next_el (cat [HD r] (cat (betwn r (HD r) (LAST r)) [LAST r])) x)`。 -/
theorem nextHdLastBetwn {α : Type*} [DecidableEq α] [Inhabited α] {r : List α}
    (hne : r ≠ []) (hnd : r.Nodup) (hne2 : r.head! ≠ r.getLast!) :
    ∀ x ∈ r,
      nextEl r x
        = nextEl ([r.head!] ++ (between r r.head! r.getLast! ++ [r.getLast!])) x := by
  intro x _
  exact congrArg (fun l => nextEl l x) (eqHdLastBetwn hne hnd hne2)

/-! ## §4 `betwn_cat`（more_lemma1.hl:1136；直证路线，免 HOL 三子件） -/

/-- **HOL `betwn_cat`**（more_lemma1.hl:1136）：
`uniq (g ++ s) ∧ y,z ∈ s ∧ indexf y z s ≤ indexf y (LAST s) s ∧ y ≠ z
⇒ betwn (g ++ s) y z = betwn s y z`。
直证：`indexf` 定义展开把不等式化归为 `s.idxOf y < s.idxOf z`（非回卷支），
再 `between_eq_take_of_idxOf_lt` 双侧 + `idxOf_append` 移位 + `drop_append` 对齐；
HOL 的 `MEM_betwn_cat`/`LAST_betwn_cat`/`next_betwn_cat` 三子件不需要。 -/
theorem betwnCat {α : Type*} [DecidableEq α] [Inhabited α]
    {g s : List α} {y z : α}
    (hnd : (g ++ s).Nodup) (hy : y ∈ s) (hz : z ∈ s)
    (hle : Kepler.Text.Reduction5.indexf y z s
      ≤ Kepler.Text.Reduction5.indexf y s.getLast! s) (hyz : y ≠ z) :
    between (g ++ s) y z = between s y z := by
  have hnds : s.Nodup := (List.nodup_append.mp hnd).2.1
  have hdisj := (List.nodup_append.mp hnd).2.2
  have hyg : y ∉ g := fun hmem => hdisj y hmem y hy rfl
  have hne : s ≠ [] := by
    intro h
    subst h
    simp at hy
  have hyi : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hzi : s.idxOf z < s.length := List.idxOf_lt_length_iff.mpr hz
  have hidxne : s.idxOf y ≠ s.idxOf z := fun he => hyz ((List.idxOf_inj hy).mp he)
  have hlastmem : s.getLast! ∈ s := by
    rw [getLastBangEqGetLast hne]
    exact List.getLast_mem hne
  have hgl : s.getLast! = s[s.length - 1]'(by omega) := by
    rw [getLastBangEqGetLast hne]
    exact List.getLast_eq_getElem hne
  have hidxlast : s.idxOf s.getLast! = s.length - 1 := by
    conv_lhs => rw [hgl]
    exact Kepler.Text.TameLp.idxOf_getElem hnds (i := s.length - 1) (by omega)
  have hval : ∀ (u v : α), u ∈ s → v ∈ s →
      Kepler.Text.Reduction5.indexf u v s
        = (s.idxOf v + (s.length - s.idxOf u)) % s.length := by
    intro u v hu hv
    unfold Kepler.Text.Reduction5.indexf
    rw [if_pos ⟨hu, hv⟩]
  have hlt : s.idxOf y < s.idxOf z := by
    by_contra hcon
    push Not at hcon
    have hzy : s.idxOf z < s.idxOf y := lt_of_le_of_ne hcon (Ne.symm hidxne)
    rw [hval y z hy hz, hval y s.getLast! hy hlastmem, hidxlast] at hle
    have e1 : (s.idxOf z + (s.length - s.idxOf y)) % s.length
        = s.length - (s.idxOf y - s.idxOf z) := by
      rw [show s.idxOf z + (s.length - s.idxOf y)
          = s.length - (s.idxOf y - s.idxOf z) from by omega,
        Nat.mod_eq_of_lt (by omega)]
    have e2 : (s.length - 1 + (s.length - s.idxOf y)) % s.length
        = s.length - 1 - s.idxOf y := by
      rw [show s.length - 1 + (s.length - s.idxOf y)
          = s.length + (s.length - 1 - s.idxOf y) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [e1, e2] at hle
    omega
  have hy' : (g ++ s).idxOf y = s.idxOf y + g.length := by
    rw [List.idxOf_append, if_neg hyg]
  have hz' : (g ++ s).idxOf z = s.idxOf z + g.length := by
    rw [List.idxOf_append, if_neg (fun hmem => hdisj z hmem z hz rfl)]
  have hlt' : (g ++ s).idxOf y < (g ++ s).idxOf z := by
    rw [hy', hz']; omega
  rw [Kepler.Text.Reduction4.between_eq_take_of_idxOf_lt hnd
        (List.mem_append_right g hy) (List.mem_append_right g hz) hlt',
      Kepler.Text.Reduction4.between_eq_take_of_idxOf_lt hnds hy hz hlt]
  rw [hy', hz']
  have hk : s.idxOf z + g.length - (s.idxOf y + g.length) - 1
      = s.idxOf z - s.idxOf y - 1 := by omega
  have hd : List.drop (s.idxOf y + g.length + 1) (g ++ s)
      = List.drop (s.idxOf y + 1) s := by
    rw [List.drop_append]
    have h1 : List.drop (s.idxOf y + g.length + 1) g = [] :=
      List.drop_eq_nil_of_le (by omega)
    rw [h1, List.nil_append]
    congr 1
    omega
  rw [hk, hd]


/-! ## §5 `HD_BETWN2`（DANGEYJ.hl:709）：`betwn` 段的头 = `next_el r r1` -/

/-- `take` 的头 = 父列表头（`0 < n`）。 -/
private theorem headBangTake {α : Type*} [Inhabited α] {l : List α} {n : ℕ}
    (hn : 0 < n) : (l.take n).head! = l.head! := by
  cases l with
  | nil =>
    cases n with
    | zero => omega
    | succ m => rfl
  | cons a t =>
    cases n with
    | zero => omega
    | succ m => rfl

/-- `drop n` 的头 = `l[n]`（`n < length`）。 -/
private theorem headBangDrop {α : Type*} [Inhabited α] {l : List α} {n : ℕ}
    (hn : n < l.length) : (l.drop n).head! = l[n]'hn := by
  induction n generalizing l with
  | zero =>
    cases l with
    | nil => simp at hn
    | cons a t => rfl
  | succ m ih =>
    cases l with
    | nil => simp at hn
    | cons a t =>
      rw [List.drop_succ_cons, ih (by simpa using hn)]
      exact (List.getElem_cons_succ a t m hn).symm

/-- **HOL `Dangeyj.HD_BETWN2`**（DANGEYJ.hl:709）：
`MEM r1 r ∧ MEM r2 r ∧ r1≠r2 ∧ uniq r ∧ ~(betwn r r1 r2=[]) ⇒
HD (betwn r r1 r2) = next_el r r1`。
证体：`idxOf` 双支（`between_eq_take/append`）+ take/drop 头两小引理 + `nextEl_eq_getD`。 -/
theorem hdBetwn2 {α : Type*} [DecidableEq α] [Inhabited α] {r : List α} {r1 r2 : α}
    (hr1 : r1 ∈ r) (hr2 : r2 ∈ r) (hne : r1 ≠ r2) (hnd : r.Nodup)
    (hne' : between r r1 r2 ≠ []) :
    (between r r1 r2).head! = nextEl r r1 := by
  have hi1 : r.idxOf r1 < r.length := List.idxOf_lt_length_iff.mpr hr1
  have hi2 : r.idxOf r2 < r.length := List.idxOf_lt_length_iff.mpr hr2
  have hidxne : r.idxOf r1 ≠ r.idxOf r2 := fun he => hne ((List.idxOf_inj hr1).mp he)
  have hpos : 0 < r.length := List.length_pos_of_mem hr1
  rcases Nat.lt_or_ge (r.idxOf r1) (r.idxOf r2) with hlt | hge
  · have hk : 0 < r.idxOf r2 - r.idxOf r1 - 1 := by
      by_contra h
      push Not at h
      apply hne'
      rw [Kepler.Text.Reduction4.between_eq_take_of_idxOf_lt hnd hr1 hr2 hlt,
        show r.idxOf r2 - r.idxOf r1 - 1 = 0 from by omega]
      rfl
    have hlt1 : r.idxOf r1 + 1 < r.length := by omega
    rw [Kepler.Text.Reduction4.between_eq_take_of_idxOf_lt hnd hr1 hr2 hlt]
    rw [headBangTake hk,
      headBangDrop (l := r) (n := r.idxOf r1 + 1) (by omega)]
    rw [Kepler.Text.TameLp.nextEl_eq_getD hr1, Nat.mod_eq_of_lt hlt1]
    exact (Kepler.Text.TameLp.getD_eq_getElem_of_lt hlt1 r1).symm
  · have hlt2 : r.idxOf r2 < r.idxOf r1 := lt_of_le_of_ne hge (Ne.symm hidxne)
    have hform : between r r1 r2
        = List.drop (r.idxOf r1 + 1) r ++ List.take (r.idxOf r2) r :=
      Kepler.Text.Reduction4.between_eq_append_of_idxOf_gt hnd hr1 hr2 hlt2
    rw [hform]
    by_cases hlast : r.idxOf r1 + 1 < r.length
    · have hne0 : List.drop (r.idxOf r1 + 1) r ≠ [] := by
        intro h
        have hlen : (List.drop (r.idxOf r1 + 1) r).length = 0 := by rw [h]; rfl
        rw [List.length_drop] at hlen
        omega
      rw [List.head!_append _ hne0, headBangDrop hlast,
        Kepler.Text.TameLp.nextEl_eq_getD hr1, Nat.mod_eq_of_lt hlast]
      exact (Kepler.Text.TameLp.getD_eq_getElem_of_lt hlast r1).symm
    · have hlastn : r.idxOf r1 + 1 = r.length := by omega
      have hdrop : List.drop (r.idxOf r1 + 1) r = [] := by
        rw [hlastn]; exact List.drop_length
      have htake : List.take (r.idxOf r2) r ≠ [] := by
        intro h
        apply hne'
        rw [hform, hdrop, h]
        rfl
      have hi2pos : 0 < r.idxOf r2 := by
        rcases Nat.eq_zero_or_pos (r.idxOf r2) with h | h
        · exfalso; apply htake; rw [h]; rfl
        · exact h
      rw [hdrop, List.nil_append, headBangTake hi2pos,
        Kepler.Text.TameLp.nextEl_eq_getD hr1,
        show (r.idxOf r1 + 1) % r.length = 0 from by rw [hlastn, Nat.mod_self],
        Kepler.Text.TameLp.getD_eq_getElem_of_lt hpos r1]
      cases r with
      | nil => simp at hr1
      | cons a t => rfl


end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.TameSpine.hdCat
#print axioms Kepler.Text.TameSpine.nextElInj
#print axioms Kepler.Text.TameSpine.eqHdLastBetwn
#print axioms Kepler.Text.TameSpine.memHdLastBetwn
#print axioms Kepler.Text.TameSpine.lastHdLastBetwn
#print axioms Kepler.Text.TameSpine.nextHdLastBetwn
#print axioms Kepler.Text.TameSpine.betwnCat
#print axioms Kepler.Text.TameSpine.hdBetwn2
