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
import Kepler.Text.TameSpine.TameList53
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList7
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList11
import Kepler.Text.TameSpine.JcajyduAqLeaf12B
import Kepler.Text.TameSpine.JcajyduAqLeaf12C
import Kepler.Text.TameSpine.JcajyduAqLeaf12D
import Kepler.Text.TameSpine.JcajyduAqLeaf12I
import Kepler.Text.TameSpine.JcajyduAqLeaf12J
import Kepler.Text.TameSpine.JcajyduAqLeaf12T
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.Reduction3Thm6B
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.JcajyduAqLeaf8W0
import Kepler.Text.TameSpine.JcajyduAqLeaf12A

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (nextEl prevEl fList eList GoodList)
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


/-! ## §6 `EQ_MEM_NEXT_EL_LAST`（AQ4.hl:60）与 `next_el_betwn_same`（NCVIBWU.hl:131）

两件是 `parts_betwn`（more_lemma1.hl:471）与 cat 族的索引代数内核：
`indexf` 模移位 + `indexlBetwn`/`sizeBetwn`/`indexfBetwnEq` 的环算术。 -/

/-- `next_el` 步进下 `indexf y · f` 的模移位：
`indexf y (next_el f d) f = (indexf y d f + 1) % f.length`（成员态）。 -/
private theorem indexfNextEl {α : Type} [DecidableEq α] {f : List α} {y d : α}
    (hnd : f.Nodup) (hy : y ∈ f) (hd : d ∈ f) :
    Kepler.Text.Reduction5.indexf y (nextEl f d) f
      = (Kepler.Text.Reduction5.indexf y d f + 1) % f.length := by
  have hpos : 0 < f.length := List.length_pos_of_mem hd
  have hnextmem : nextEl f d ∈ f := Kepler.Text.TameLp.nextEl_mem_of_mem hd
  have hi : f.idxOf (nextEl f d) = (f.idxOf d + 1) % f.length := by
    rw [Kepler.Text.TameLp.nextEl_eq_getD hd,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
    exact Kepler.Text.TameLp.idxOf_getElem hnd (Nat.mod_lt _ hpos)
  have hival : Kepler.Text.Reduction5.indexf y d f
      = (f.idxOf d + (f.length - f.idxOf y)) % f.length := by
    unfold Kepler.Text.Reduction5.indexf
    rw [if_pos ⟨hy, hd⟩]
  have hival2 : Kepler.Text.Reduction5.indexf y (nextEl f d) f
      = (f.idxOf (nextEl f d) + (f.length - f.idxOf y)) % f.length := by
    unfold Kepler.Text.Reduction5.indexf
    rw [if_pos ⟨hy, hnextmem⟩]
  rw [hival, hival2, hi, Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

/-- `indexf y d f = indexf y z f - 1` ⇒ `d` 是 `betwn f y z` 的末元。 -/
private theorem betwnGetLastOfIndexfSucc {α : Type} [DecidableEq α] [Inhabited α]
    {f : List α} {y z d : α} (hyz : y ≠ z) (hy : y ∈ f) (hz : z ∈ f)
    (hd : d ∈ between f y z) (hnd : f.Nodup)
    (hidx : Kepler.Text.Reduction5.indexf y d f
      = Kepler.Text.Reduction5.indexf y z f - 1) :
    (between f y z).getLast! = d := by
  have hBne : between f y z ≠ [] := fun h => by rw [h] at hd; simp at hd
  have h1 : (between f y z).idxOf d + 1 = Kepler.Text.Reduction5.indexf y d f :=
    Kepler.Text.Reduction5.indexlBetwn hnd hyz hy hz hd
  have h2 : (between f y z).length = Kepler.Text.Reduction5.indexf y z f - 1 :=
    Kepler.Text.Reduction5.sizeBetwn hnd hy hz hyz
  have h3 : (between f y z).idxOf d = (between f y z).length - 1 := by omega
  have hmemlast : (between f y z).getLast! ∈ between f y z := by
    rw [getLastBangEqGetLast hBne]
    exact List.getLast_mem hBne
  have hgl : (between f y z).getLast!
      = (between f y z)[(between f y z).length - 1]'(by omega) := by
    rw [getLastBangEqGetLast hBne]
    exact List.getLast_eq_getElem hBne
  have hidxl : (between f y z).idxOf ((between f y z).getLast!)
      = (between f y z).length - 1 := by
    conv_lhs => rw [hgl]
    exact Kepler.Text.TameLp.idxOf_getElem (Kepler.Graphs.between_distinct hnd)
      (i := (between f y z).length - 1) (by omega)
  exact (List.idxOf_inj hmemlast).mp (by rw [hidxl, h3])

/-- **HOL `Aq4.EQ_MEM_NEXT_EL_LAST`**（AQ4.hl:60）：
`¬(y=z) ∧ y,z∈f ∧ d∈betwn f y z ∧ uniq f ⇒
(MEM (next_el f d) (betwn f y z) ↔ ~(LAST(betwn f y z)=d))`。
正向：`d = last B ⇒ next_el d = z`（`nextLastBetwn`）撞 `notBetwn2`；
反向：`indexf` 模移位 + 「末元 ⇔ indexf = indexf z - 1」。 -/
theorem eqMemNextElLast {α : Type} [DecidableEq α] [Inhabited α]
    {f : List α} {y z d : α}
    (hyz : y ≠ z) (hy : y ∈ f) (hz : z ∈ f)
    (hd : d ∈ between f y z) (hnd : f.Nodup) :
    (nextEl f d ∈ between f y z) ↔ (between f y z).getLast! ≠ d := by
  have hdf : d ∈ f := Kepler.Text.Reduction5.betwnMem hd
  have hBne : between f y z ≠ [] := fun h => by rw [h] at hd; simp at hd
  constructor
  · intro hmem hgl
    have hz1 : nextEl f d = z := by
      rw [← hgl, show (between f y z).getLast!
          = (between f y z).getLast hBne from getLastBangEqGetLast hBne]
      exact Kepler.Text.Reduction5.nextLastBetwn hy hz hnd hyz hBne
    rw [hz1] at hmem
    exact (Kepler.Text.Reduction4.notBetwn2 hnd) hmem
  · intro hgl
    have hI := (Kepler.Text.Reduction5.indexfBetwnEq hyz hnd hy hz).mp hd
    have hzlt : Kepler.Text.Reduction5.indexf y z f < f.length :=
      Kepler.Text.Reduction5.indexfLtSizel hy hz
    have hne2 : Kepler.Text.Reduction5.indexf y d f
        ≠ Kepler.Text.Reduction5.indexf y z f - 1 :=
      fun he => hgl (betwnGetLastOfIndexfSucc hyz hy hz hd hnd he)
    have hlt2 : Kepler.Text.Reduction5.indexf y d f + 1
        < Kepler.Text.Reduction5.indexf y z f := by omega
    have hltn : Kepler.Text.Reduction5.indexf y d f + 1 < f.length := by omega
    have hstep := indexfNextEl hnd hy hdf
    refine (Kepler.Text.Reduction5.indexfBetwnEq hyz hnd hy hz).mpr ⟨?_, ?_⟩
    · rw [hstep, Nat.mod_eq_of_lt hltn]
      omega
    · rw [hstep, Nat.mod_eq_of_lt hltn]
      omega

/-- 同下标 `getElem` 相等（证明参数无关；AGENTS §7.1 #10 口径）。 -/
private theorem getElemEqOfEqIdx {α : Type*} {l : List α} {i j : ℕ}
    (hij : i = j) (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst hij
  rfl

/-- **HOL `Ncvibwu.next_el_betwn_same`**（NCVIBWU.hl:131）：
`¬(y=z) ∧ y,z∈f ∧ d∈betwn f y z ∧ next_el f d ∈ betwn f y z ∧ uniq f ⇒
next_el (betwn f y z) d = next_el f d`。
证体：`indexlBetwn`×2 + `sizeBetwn` + `indexf` 模移位 ⇒
`B.idxOf (next_el d) = B.idxOf d + 1`（模坍缩支由 `nextLastBetwn`+`notBetwn2` 排除）。 -/
theorem nextElBetwnSame {α : Type} [DecidableEq α] [Inhabited α]
    {f : List α} {y z d : α}
    (hyz : y ≠ z) (hy : y ∈ f) (hz : z ∈ f) (hd : d ∈ between f y z)
    (hnext : nextEl f d ∈ between f y z) (hnd : f.Nodup) :
    nextEl (between f y z) d = nextEl f d := by
  have hdf : d ∈ f := Kepler.Text.Reduction5.betwnMem hd
  have hBnd : (between f y z).Nodup := Kepler.Graphs.between_distinct hnd
  have hBne : between f y z ≠ [] := fun h => by rw [h] at hd; simp at hd
  have hin1 : (between f y z).idxOf d + 1 = Kepler.Text.Reduction5.indexf y d f :=
    Kepler.Text.Reduction5.indexlBetwn hnd hyz hy hz hd
  have hin2 : (between f y z).idxOf (nextEl f d) + 1
      = Kepler.Text.Reduction5.indexf y (nextEl f d) f :=
    Kepler.Text.Reduction5.indexlBetwn hnd hyz hy hz hnext
  have hL : (between f y z).length = Kepler.Text.Reduction5.indexf y z f - 1 :=
    Kepler.Text.Reduction5.sizeBetwn hnd hy hz hyz
  have hzlt : Kepler.Text.Reduction5.indexf y z f < f.length :=
    Kepler.Text.Reduction5.indexfLtSizel hy hz
  have hidxnextlt : (between f y z).idxOf (nextEl f d) < (between f y z).length :=
    List.idxOf_lt_length_iff.mpr hnext
  have hstep := indexfNextEl hnd hy hdf
  have hexp : (between f y z).idxOf (nextEl f d) + 1
      = ((between f y z).idxOf d + 2) % f.length := by
    rw [hin2, hstep, ← hin1]
  have hmlt : (between f y z).idxOf d + 2 < f.length := by
    have hI := (Kepler.Text.Reduction5.indexfBetwnEq hyz hnd hy hz).mp hd
    omega
  have hidxeq : (between f y z).idxOf (nextEl f d)
      = (between f y z).idxOf d + 1 := by
    rw [Nat.mod_eq_of_lt hmlt] at hexp
    omega
  -- nextEl B d = B[B.idxOf d + 1] = B[B.idxOf (nextEl d)] = nextEl f d
  have hposB : 0 < (between f y z).length := List.length_pos_iff.mpr hBne
  have hnextB : nextEl (between f y z) d
      = (between f y z)[((between f y z).idxOf d + 1) % (between f y z).length]'
          (Nat.mod_lt _ hposB) := by
    rw [Kepler.Text.TameLp.nextEl_eq_getD hd,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt (Nat.mod_lt _ hposB)]
  rw [hnextB]
  have hidxmod : ((between f y z).idxOf d + 1) % (between f y z).length
      = (between f y z).idxOf d + 1 := Nat.mod_eq_of_lt (by omega)
  exact (getElemEqOfEqIdx (l := between f y z) hidxmod
      (Nat.mod_lt _ hposB) (by omega)).trans
    ((getElemEqOfEqIdx (l := between f y z) hidxeq.symm (by omega)
      hidxnextlt).trans (Kepler.Text.TameLp.getElem_idxOf hnext))


/-! ## §7 cat 族（more_lemma1.hl:1631-:1985）：
`next_cat_betwn_same_power` / `indexf_cat_betwn_same(_1)` /
`mem_cat_betwn_same` / `LAST_cat_betwn_same` / `cat_betwn_same`

统一语境：`s = [y] ++ (betwn r y z ++ [z])`（r 的 y→z 弧）。 -/

/-- 弧内成员 ⇒ r 成员。 -/
private theorem memOfArc {r s : List Dart} {y z : Dart}
    (hy : y ∈ r) (hz : z ∈ r) (hs : s = [y] ++ (between r y z ++ [z])) :
    ∀ a ∈ s, a ∈ r := by
  intro a ha
  rw [hs] at ha
  rcases List.mem_append.mp ha with h1 | h2
  · rw [List.mem_singleton] at h1
    rw [h1]; exact hy
  · rcases List.mem_append.mp h2 with h3 | h4
    · exact Kepler.Graphs.inbetween_inset h3
    · rw [List.mem_singleton] at h4
      rw [h4]; exact hz

/-- **HOL `next_cat_betwn_same_power`**（more_lemma1.hl:1631）：
弧内幂行走两侧一致（`n ≤ indexf lx z s`）。 -/
theorem nextCatBetwnSamePower {r s : List Dart} {y z lx : Dart}
    (hnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hyz : y ≠ z)
    (hs : s = [y] ++ (between r y z ++ [z])) (hlx : lx ∈ s) :
    ∀ n : ℕ, n ≤ Kepler.Text.Reduction5.indexf lx z s →
      (nextEl s)^[n] lx = (nextEl r)^[n] lx := by
  have hsnd : s.Nodup := by
    rw [hs]
    exact Kepler.Text.TameSpine.uniqAppendBetwn hnd hy hz hyz
  have hzs : z ∈ s := by rw [hs]; simp
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hk' : k ≤ Kepler.Text.Reduction5.indexf lx z s := by omega
    have hklt : k < Kepler.Text.Reduction5.indexf lx z s := by omega
    have hidxlt : Kepler.Text.Reduction5.indexf lx z s < s.length :=
      Kepler.Text.Reduction5.indexfLtSizel hlx hzs
    have hd_eq : (nextEl s)^[k] lx = (nextEl r)^[k] lx := ih hk'
    have hds : (nextEl s)^[k] lx ∈ s := by
      have key : ∀ m : ℕ, (nextEl s)^[m] lx ∈ s := by
        intro m
        induction m with
        | zero => simpa using hlx
        | succ m ihm =>
          rw [Function.iterate_succ_apply']
          exact Kepler.Text.TameLp.nextEl_mem_of_mem ihm
      exact key k
    have hds' : (nextEl r)^[k] lx ∈ s := hd_eq ▸ hds
    have hdz : (nextEl r)^[k] lx ≠ z := by
      intro hcon
      have h1 : (nextEl s)^[k] lx = z := by rw [hd_eq]; exact hcon
      have h2 : Kepler.Text.Reduction5.indexf lx z s = k := by
        have h := Kepler.Text.TameSpine.nextElnIndexf hlx hzs hsnd h1 (by omega)
        rwa [← Kepler.Text.Reduction3.indexf_eq_spine lx z s] at h
      omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hd_eq]
    exact Kepler.Text.TameSpine.nextCatBetwnSame r hnd hz hy (Ne.symm hyz) hds' hs hdz

/-- **HOL `indexf_cat_betwn_same`**（more_lemma1.hl:1676）：
`indexf lx lz s ≤ indexf lx z s ⇒ indexf lx lz s = indexf lx lz r`。 -/
theorem indexfCatBetwnSame {r s : List Dart} {y z lx lz : Dart}
    (hnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hyz : y ≠ z)
    (hs : s = [y] ++ (between r y z ++ [z]))
    (hlx : lx ∈ s) (hlz : lz ∈ s)
    (hle : Kepler.Text.Reduction5.indexf lx lz s
      ≤ Kepler.Text.Reduction5.indexf lx z s) :
    Kepler.Text.Reduction5.indexf lx lz s
      = Kepler.Text.Reduction5.indexf lx lz r := by
  have hsnd : s.Nodup := by
    rw [hs]; exact Kepler.Text.TameSpine.uniqAppendBetwn hnd hy hz hyz
  have hzs : z ∈ s := by rw [hs]; simp
  have hmemr := memOfArc hy hz hs
  have hlxr : lx ∈ r := hmemr lx hlx
  have hlzr : lz ∈ r := hmemr lz hlz
  have hlen : s.length = Kepler.Text.Reduction5.indexf y z r + 1 := by
    have hB : (between r y z).length = Kepler.Text.TameSpine.indexf y z r - 1 :=
      Kepler.Text.TameSpine.sizeBetwn hnd hy hz hyz
    rw [← Kepler.Text.Reduction3.indexf_eq_spine y z r] at hB
    rw [hs, List.length_append, List.length_append, List.length_singleton,
      List.length_singleton]
    have hpos : 0 < Kepler.Text.Reduction5.indexf y z r := by
      rcases Nat.eq_zero_or_pos (Kepler.Text.Reduction5.indexf y z r) with h0 | h1
      · exact absurd (Kepler.Text.Reduction4.indexf_eq_zero hy hz h0) hyz
      · exact h1
    omega
  have hlt : Kepler.Text.Reduction5.indexf lx lz s < r.length := by
    have h1 : Kepler.Text.Reduction5.indexf lx lz s < s.length :=
      Kepler.Text.Reduction5.indexfLtSizel hlx hlz
    have h2 : Kepler.Text.Reduction5.indexf y z r < r.length :=
      Kepler.Text.Reduction5.indexfLtSizel hy hz
    omega
  have hpow := nextCatBetwnSamePower hnd hy hz hyz hs hlx
    (Kepler.Text.Reduction5.indexf lx lz s) hle
  have hiterS : (nextEl s)^[Kepler.Text.Reduction5.indexf lx lz s] lx = lz := by
    have h := Kepler.Text.TameSpine.indexfN hlx hlz hsnd
    rwa [← Kepler.Text.Reduction3.indexf_eq_spine lx lz s] at h
  have hiterR : (nextEl r)^[Kepler.Text.Reduction5.indexf lx lz s] lx = lz :=
    hpow.symm.trans hiterS
  have hfin := Kepler.Text.TameSpine.nextElnIndexf hlxr hlzr hnd hiterR hlt
  rw [← Kepler.Text.Reduction3.indexf_eq_spine lx lz r] at hfin
  exact hfin.symm

/-- **HOL `indexf_cat_betwn_same1`**（more_lemma1.hl:1725）：
`indexf lx lz r ≤ indexf lx z s ⇒ indexf lx lz s = indexf lx lz r`。 -/
theorem indexfCatBetwnSame1 {r s : List Dart} {y z lx lz : Dart}
    (hnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hyz : y ≠ z)
    (hs : s = [y] ++ (between r y z ++ [z]))
    (hlx : lx ∈ s) (hlz : lz ∈ s)
    (hle : Kepler.Text.Reduction5.indexf lx lz r
      ≤ Kepler.Text.Reduction5.indexf lx z s) :
    Kepler.Text.Reduction5.indexf lx lz s
      = Kepler.Text.Reduction5.indexf lx lz r := by
  have hsnd : s.Nodup := by
    rw [hs]; exact Kepler.Text.TameSpine.uniqAppendBetwn hnd hy hz hyz
  have hzs : z ∈ s := by rw [hs]; simp
  have hmemr := memOfArc hy hz hs
  have hlxr : lx ∈ r := hmemr lx hlx
  have hlzr : lz ∈ r := hmemr lz hlz
  have hpow := nextCatBetwnSamePower hnd hy hz hyz hs hlx
    (Kepler.Text.Reduction5.indexf lx lz r) hle
  have hiterR : (nextEl r)^[Kepler.Text.Reduction5.indexf lx lz r] lx = lz := by
    have h := Kepler.Text.TameSpine.indexfN hlxr hlzr hnd
    rwa [← Kepler.Text.Reduction3.indexf_eq_spine lx lz r] at h
  have hiterS : (nextEl s)^[Kepler.Text.Reduction5.indexf lx lz r] lx = lz :=
    hpow.trans hiterR
  have hlt : Kepler.Text.Reduction5.indexf lx lz r < s.length := by
    have h1 : Kepler.Text.Reduction5.indexf lx z s < s.length :=
      Kepler.Text.Reduction5.indexfLtSizel hlx hzs
    omega
  have hfin := Kepler.Text.TameSpine.nextElnIndexf hlx hlz hsnd hiterS hlt
  rwa [← Kepler.Text.Reduction3.indexf_eq_spine lx lz s] at hfin


/-! ## §8 cat 族本体（more_lemma1.hl:1769/:1840/:1941）：
`mem_cat_betwn_same` / `LAST_cat_betwn_same` / `cat_betwn_same`

统一语境同 §7：`s = [y] ++ (betwn r y z ++ [z])`。R1 口径（沿 §2/§7 实测）：陈述的
`between`/`nextEl` 在 Dart 默认实例世界；成员↔indexf 判定一律走 BEq-多态
`TameSpine.indexfBetwnEq`（其 `between` 随目标实例统一），`indexf` 值经
`Reduction3Thm6B.indexf_eq_spine` 在 `Reduction5.indexf` ↔ `TameSpine.indexf`
间折桥；不直接消费链侧 `[DecidableEq]` 世界的 between 件（R1 碰撞）。 -/

/-- 幂行走成员（BEq 世界泛型；§8 反向支用）。 -/
private theorem memNextElIterateG {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hx : x ∈ s) : ∀ k : ℕ, (nextEl s)^[k] x ∈ s := by
  intro k
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Kepler.Text.TameLp.nextEl_mem_of_mem ih

/-- 弧 `betwn f a b` 末元的 `indexf` 值恰为 `indexf a b - 1`（BEq 世界）。 -/
private theorem lastIndexfGetLastG {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    [Inhabited α] {f : List α} {a b : α} (hab : a ≠ b) (ha : a ∈ f) (hb : b ∈ f)
    (hnd : f.Nodup) (hBne : between f a b ≠ []) :
    Kepler.Text.TameSpine.indexf a (between f a b).getLast! f
      = Kepler.Text.TameSpine.indexf a b f - 1 := by
  have hBnd : (between f a b).Nodup := Kepler.Graphs.between_distinct hnd
  have hpos : 0 < (between f a b).length := List.length_pos_of_ne_nil hBne
  have hd : (between f a b).getLast! ∈ between f a b := by
    rw [getLastBangEqGetLast hBne]
    exact List.getLast_mem hBne
  have h1 : (between f a b).idxOf (between f a b).getLast! + 1
      = Kepler.Text.TameSpine.indexf a (between f a b).getLast! f :=
    Kepler.Text.TameSpine.indexlBetwn hnd ha hb hd
  have h2 : (between f a b).length = Kepler.Text.TameSpine.indexf a b f - 1 :=
    Kepler.Text.TameSpine.sizeBetwn hnd ha hb hab
  have hgl : (between f a b).getLast!
      = (between f a b)[(between f a b).length - 1]'(by omega) := by
    rw [getLastBangEqGetLast hBne]
    exact List.getLast_eq_getElem hBne
  have h3 : (between f a b).idxOf (between f a b).getLast!
      = (between f a b).length - 1 := by
    conv_lhs => rw [hgl]
    exact Kepler.Text.TameLp.idxOf_getElem hBnd
      (i := (between f a b).length - 1) (by omega)
  omega

/-- 「弧内元的 `indexf` 恰为 `indexf a b - 1`」⇒ 它是弧的末元（BEq 世界；
§6 `betwnGetLastOfIndexfSucc` 的泛型孪生，避开 R1 实例碰撞）。 -/
private theorem betwnGetLastOfIndexfSuccG {α : Type} [BEq α] [LawfulBEq α]
    [DecidableEq α] [Inhabited α] {f : List α} {a b d : α} (hab : a ≠ b)
    (ha : a ∈ f) (hb : b ∈ f) (hd : d ∈ between f a b) (hnd : f.Nodup)
    (hidx : Kepler.Text.TameSpine.indexf a d f
      = Kepler.Text.TameSpine.indexf a b f - 1) :
    (between f a b).getLast! = d := by
  have hBne : between f a b ≠ [] := fun h => by rw [h] at hd; simp at hd
  have hpos : 0 < (between f a b).length := List.length_pos_of_ne_nil hBne
  have h1 : (between f a b).idxOf d + 1 = Kepler.Text.TameSpine.indexf a d f :=
    Kepler.Text.TameSpine.indexlBetwn hnd ha hb hd
  have h2 : (between f a b).length = Kepler.Text.TameSpine.indexf a b f - 1 :=
    Kepler.Text.TameSpine.sizeBetwn hnd ha hb hab
  have h3 : (between f a b).idxOf d = (between f a b).length - 1 := by omega
  have hmemlast : (between f a b).getLast! ∈ between f a b := by
    rw [getLastBangEqGetLast hBne]
    exact List.getLast_mem hBne
  have hgl : (between f a b).getLast!
      = (between f a b)[(between f a b).length - 1]'(by omega) := by
    rw [getLastBangEqGetLast hBne]
    exact List.getLast_eq_getElem hBne
  have hidxl : (between f a b).idxOf ((between f a b).getLast!)
      = (between f a b).length - 1 := by
    conv_lhs => rw [hgl]
    exact Kepler.Text.TameLp.idxOf_getElem (Kepler.Graphs.between_distinct hnd)
      (i := (between f a b).length - 1) (by omega)
  exact (List.idxOf_inj hmemlast).mp (by rw [hidxl, h3])

/-- **HOL `mem_cat_betwn_same`**（more_lemma1.hl:1769）：
`s = [y]++(betwn r y z++[z]) ∧ uniq r ∧ y,z∈r ∧ y≠z ∧ lx,lz∈s ∧ lx≠lz ∧
indexf lx lz s ≤ indexf lx z s ⇒ ∀x, x∈betwn s lx lz ↔ x∈betwn r lx lz`。
证体沿 HOL：两侧 `indexfBetwnEq` + `indexfCatBetwnSame(_1)` 转移；反向支以
`indexf_n` + `next_cat_betwn_same_power` 幂行走给出 `x∈s`。 -/
theorem memCatBetwnSame {r s : List Dart} {y z lx lz : Dart}
    (hnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hyz : y ≠ z)
    (hs : s = [y] ++ (between r y z ++ [z]))
    (hlx : lx ∈ s) (hlz : lz ∈ s) (hlxzlz : lx ≠ lz)
    (hle : Kepler.Text.Reduction5.indexf lx lz s
      ≤ Kepler.Text.Reduction5.indexf lx z s) :
    ∀ x, x ∈ between s lx lz ↔ x ∈ between r lx lz := by
  have hsnd : s.Nodup := by
    rw [hs]; exact Kepler.Text.TameSpine.uniqAppendBetwn hnd hy hz hyz
  have hmemr := memOfArc hy hz hs
  have hlxr : lx ∈ r := hmemr lx hlx
  have hlzr : lz ∈ r := hmemr lz hlz
  have elz : Kepler.Text.Reduction5.indexf lx lz s
      = Kepler.Text.Reduction5.indexf lx lz r :=
    indexfCatBetwnSame hnd hy hz hyz hs hlx hlz hle
  intro x
  constructor
  · intro hx
    have hxs : x ∈ s := Kepler.Graphs.inbetween_inset hx
    have hIs := (Kepler.Text.TameSpine.indexfBetwnEq hlxzlz hsnd hlx hlz).mp hx
    have hIs' : 0 < Kepler.Text.Reduction5.indexf lx x s
        ∧ Kepler.Text.Reduction5.indexf lx x s
          < Kepler.Text.Reduction5.indexf lx lz s := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine lx x s,
        Kepler.Text.Reduction3.indexf_eq_spine lx lz s]
      exact hIs
    have ex : Kepler.Text.Reduction5.indexf lx x s
        = Kepler.Text.Reduction5.indexf lx x r :=
      indexfCatBetwnSame hnd hy hz hyz hs hlx hxs (by omega)
    refine (Kepler.Text.TameSpine.indexfBetwnEq hlxzlz hnd hlxr hlzr).mpr ⟨?_, ?_⟩
    · rw [← Kepler.Text.Reduction3.indexf_eq_spine lx x r]; omega
    · rw [← Kepler.Text.Reduction3.indexf_eq_spine lx x r,
        ← Kepler.Text.Reduction3.indexf_eq_spine lx lz r]
      omega
  · intro hx
    have hxr : x ∈ r := Kepler.Graphs.inbetween_inset hx
    have hIr := (Kepler.Text.TameSpine.indexfBetwnEq hlxzlz hnd hlxr hlzr).mp hx
    have hIr' : 0 < Kepler.Text.Reduction5.indexf lx x r
        ∧ Kepler.Text.Reduction5.indexf lx x r
          < Kepler.Text.Reduction5.indexf lx lz r := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine lx x r,
        Kepler.Text.Reduction3.indexf_eq_spine lx lz r]
      exact hIr
    have hiterR := Kepler.Text.TameSpine.indexfN hlxr hxr hnd
    rw [← Kepler.Text.Reduction3.indexf_eq_spine lx x r] at hiterR
    have hxeq : (nextEl s)^[Kepler.Text.Reduction5.indexf lx x r] lx = x := by
      rw [nextCatBetwnSamePower hnd hy hz hyz hs hlx
        (Kepler.Text.Reduction5.indexf lx x r) (by omega)]
      exact hiterR
    have hxs : x ∈ s := by
      rw [← hxeq]
      exact memNextElIterateG hlx _
    have ex1 : Kepler.Text.Reduction5.indexf lx x s
        = Kepler.Text.Reduction5.indexf lx x r :=
      indexfCatBetwnSame1 hnd hy hz hyz hs hlx hxs (by omega)
    refine (Kepler.Text.TameSpine.indexfBetwnEq hlxzlz hsnd hlx hlz).mpr ⟨?_, ?_⟩
    · rw [← Kepler.Text.Reduction3.indexf_eq_spine lx x s]; omega
    · rw [← Kepler.Text.Reduction3.indexf_eq_spine lx x s,
        ← Kepler.Text.Reduction3.indexf_eq_spine lx lz s]
      omega

/-- **HOL `LAST_cat_betwn_same`**（more_lemma1.hl:1840）：
同前件 ⇒ `LAST (betwn s lx lz) = LAST (betwn r lx lz)`。
空支：`betwnNil` + `next_cat_betwn_same` 传播空性；非空支：末元 `indexf` 刻画
（`lastIndexfGetLastG`）+ `indexfCatBetwnSame` 转移 + `betwnGetLastOfIndexfSuccG`
收口。 -/
theorem lastCatBetwnSame {r s : List Dart} {y z lx lz : Dart}
    (hnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hyz : y ≠ z)
    (hs : s = [y] ++ (between r y z ++ [z]))
    (hlx : lx ∈ s) (hlz : lz ∈ s) (hlxzlz : lx ≠ lz)
    (hle : Kepler.Text.Reduction5.indexf lx lz s
      ≤ Kepler.Text.Reduction5.indexf lx z s) :
    (between s lx lz).getLast! = (between r lx lz).getLast! := by
  have hsnd : s.Nodup := by
    rw [hs]; exact Kepler.Text.TameSpine.uniqAppendBetwn hnd hy hz hyz
  have hzs : z ∈ s := by rw [hs]; simp
  have hmemr := memOfArc hy hz hs
  have hlxr : lx ∈ r := hmemr lx hlx
  have hlzr : lz ∈ r := hmemr lz hlz
  have hlxz : lx ≠ z := by
    intro hcon
    have hle' := hle
    rw [hcon] at hle'
    rw [Kepler.Text.Reduction4.indexfRefl hzs] at hle'
    have h0 : Kepler.Text.Reduction5.indexf z lz s = 0 :=
      le_antisymm hle' (Nat.zero_le _)
    exact hlxzlz (hcon.trans (Kepler.Text.Reduction4.indexf_eq_zero hzs hlz h0))
  have elz : Kepler.Text.Reduction5.indexf lx lz s
      = Kepler.Text.Reduction5.indexf lx lz r :=
    indexfCatBetwnSame hnd hy hz hyz hs hlx hlz hle
  by_cases hBs : between s lx lz = []
  · have hnil := (Kepler.Text.TameSpine.betwnNil hsnd hlxzlz hlx hlz).mp hBs
    have hnexteq : nextEl s lx = nextEl r lx :=
      Kepler.Text.TameSpine.nextCatBetwnSame r hnd hz hy (Ne.symm hyz) hlx hs hlxz
    have hr0 : between r lx lz = [] :=
      (Kepler.Text.TameSpine.betwnNil hnd hlxzlz hlxr hlzr).mpr
        (by rw [← hnexteq]; exact hnil)
    rw [hBs, hr0]
  · have hd_s : (between s lx lz).getLast! ∈ between s lx lz := by
      rw [getLastBangEqGetLast hBs]; exact List.getLast_mem hBs
    have hBdI := (Kepler.Text.TameSpine.indexfBetwnEq hlxzlz hsnd hlx hlz).mp hd_s
    have hBdI' : 0 < Kepler.Text.Reduction5.indexf lx (between s lx lz).getLast! s
        ∧ Kepler.Text.Reduction5.indexf lx (between s lx lz).getLast! s
          < Kepler.Text.Reduction5.indexf lx lz s := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine lx (between s lx lz).getLast! s,
        Kepler.Text.Reduction3.indexf_eq_spine lx lz s]
      exact hBdI
    have hidxs : Kepler.Text.Reduction5.indexf lx (between s lx lz).getLast! s
        = Kepler.Text.Reduction5.indexf lx lz s - 1 := by
      rw [Kepler.Text.Reduction3.indexf_eq_spine lx (between s lx lz).getLast! s,
        Kepler.Text.Reduction3.indexf_eq_spine lx lz s]
      exact lastIndexfGetLastG hlxzlz hlx hlz hsnd hBs
    have hd_ss : (between s lx lz).getLast! ∈ s :=
      Kepler.Graphs.inbetween_inset hd_s
    have hd_r : Kepler.Text.Reduction5.indexf lx (between s lx lz).getLast! r
        = Kepler.Text.Reduction5.indexf lx lz r - 1 := by
      have htr : Kepler.Text.Reduction5.indexf lx (between s lx lz).getLast! s
          = Kepler.Text.Reduction5.indexf lx (between s lx lz).getLast! r :=
        indexfCatBetwnSame hnd hy hz hyz hs hlx hd_ss (by omega)
      omega
    have hmem_r : (between s lx lz).getLast! ∈ between r lx lz := by
      refine (Kepler.Text.TameSpine.indexfBetwnEq hlxzlz hnd hlxr hlzr).mpr
        ⟨?_, ?_⟩
      · rw [← Kepler.Text.Reduction3.indexf_eq_spine lx
          (between s lx lz).getLast! r]
        omega
      · rw [← Kepler.Text.Reduction3.indexf_eq_spine lx
          (between s lx lz).getLast! r,
          ← Kepler.Text.Reduction3.indexf_eq_spine lx lz r]
        omega
    rw [Kepler.Text.Reduction3.indexf_eq_spine lx (between s lx lz).getLast! r,
      Kepler.Text.Reduction3.indexf_eq_spine lx lz r] at hd_r
    exact (betwnGetLastOfIndexfSuccG hlxzlz hlxr hlzr hmem_r hnd hd_r).symm

/-- **HOL `cat_betwn_same`**（more_lemma1.hl:1941）：
同前件 ⇒ `betwn s lx lz = betwn r lx lz`。
`aqs_eq_last_next` 收口：成员 iff（`memCatBetwnSame`）+ 末元（`lastCatBetwnSame`）
+ next_el 一致——`next_el` 展开到弧内同一落点下标 `p`，两侧落点经 `indexf`
单射（`indexfInj`）判等，免 HOL 的 HD/last 拆支与 R1 实例碰撞。 -/
theorem catBetwnSame {r s : List Dart} {y z lx lz : Dart}
    (hnd : r.Nodup) (hy : y ∈ r) (hz : z ∈ r) (hyz : y ≠ z)
    (hs : s = [y] ++ (between r y z ++ [z]))
    (hlx : lx ∈ s) (hlz : lz ∈ s) (hlxzlz : lx ≠ lz)
    (hle : Kepler.Text.Reduction5.indexf lx lz s
      ≤ Kepler.Text.Reduction5.indexf lx z s) :
    between s lx lz = between r lx lz := by
  have hsnd : s.Nodup := by
    rw [hs]; exact Kepler.Text.TameSpine.uniqAppendBetwn hnd hy hz hyz
  have hmemr := memOfArc hy hz hs
  have hlxr : lx ∈ r := hmemr lx hlx
  have hlzr : lz ∈ r := hmemr lz hlz
  have hmem : ∀ x, x ∈ between s lx lz ↔ x ∈ between r lx lz :=
    memCatBetwnSame hnd hy hz hyz hs hlx hlz hlxzlz hle
  have hlast : (between s lx lz).getLast! = (between r lx lz).getLast! :=
    lastCatBetwnSame hnd hy hz hyz hs hlx hlz hlxzlz hle
  refine Kepler.Text.TameSpine.aqs_eq_last_next
    (Kepler.Graphs.between_distinct hnd) (Kepler.Graphs.between_distinct hsnd)
    hmem ?_ hlast
  intro x hx
  have hxr : x ∈ between r lx lz := (hmem x).mp hx
  have hxs : x ∈ s := Kepler.Graphs.inbetween_inset hx
  have hsndB : (between s lx lz).Nodup := Kepler.Graphs.between_distinct hsnd
  have hrndB : (between r lx lz).Nodup := Kepler.Graphs.between_distinct hnd
  have hneB : between s lx lz ≠ [] := fun h => by rw [h] at hx; simp at hx
  have hneR : between r lx lz ≠ [] := fun h => by rw [h] at hxr; simp at hxr
  have hposB : 0 < (between s lx lz).length := List.length_pos_of_ne_nil hneB
  have hposR : 0 < (between r lx lz).length := List.length_pos_of_ne_nil hneR
  have hLs : (between s lx lz).length
      = Kepler.Text.Reduction5.indexf lx lz s - 1 := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine lx lz s]
    exact Kepler.Text.TameSpine.sizeBetwn hsnd hlx hlz hlxzlz
  have hLr : (between r lx lz).length
      = Kepler.Text.Reduction5.indexf lx lz r - 1 := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine lx lz r]
    exact Kepler.Text.TameSpine.sizeBetwn hnd hlxr hlzr hlxzlz
  have hIs := (Kepler.Text.TameSpine.indexfBetwnEq hlxzlz hsnd hlx hlz).mp hx
  have hIs' : 0 < Kepler.Text.Reduction5.indexf lx x s
      ∧ Kepler.Text.Reduction5.indexf lx x s
        < Kepler.Text.Reduction5.indexf lx lz s := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine lx x s,
      Kepler.Text.Reduction3.indexf_eq_spine lx lz s]
    exact hIs
  have ex : Kepler.Text.Reduction5.indexf lx x s
      = Kepler.Text.Reduction5.indexf lx x r :=
    indexfCatBetwnSame hnd hy hz hyz hs hlx hxs (by omega)
  have elz : Kepler.Text.Reduction5.indexf lx lz s
      = Kepler.Text.Reduction5.indexf lx lz r :=
    indexfCatBetwnSame hnd hy hz hyz hs hlx hlz hle
  have hi1 : (between s lx lz).idxOf x + 1
      = Kepler.Text.Reduction5.indexf lx x s := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine lx x s]
    exact Kepler.Text.TameSpine.indexlBetwn hsnd hlx hlz hx
  have hi2 : (between r lx lz).idxOf x + 1
      = Kepler.Text.Reduction5.indexf lx x r := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine lx x r]
    exact Kepler.Text.TameSpine.indexlBetwn hnd hlxr hlzr hxr
  have hps : ((between s lx lz).idxOf x + 1) % (between s lx lz).length
      < (between s lx lz).length := Nat.mod_lt _ hposB
  have hpr : ((between r lx lz).idxOf x + 1) % (between r lx lz).length
      < (between r lx lz).length := Nat.mod_lt _ hposR
  have hpEq : ((between s lx lz).idxOf x + 1) % (between s lx lz).length
      = ((between r lx lz).idxOf x + 1) % (between r lx lz).length := by
    rw [hi1, hi2, hLs, hLr, ← ex, ← elz]
  have hws : (between s lx lz)[((between s lx lz).idxOf x + 1)
      % (between s lx lz).length]'hps ∈ between s lx lz := List.getElem_mem hps
  have hws_s : (between s lx lz)[((between s lx lz).idxOf x + 1)
      % (between s lx lz).length]'hps ∈ s := Kepler.Graphs.inbetween_inset hws
  have hwr : (between r lx lz)[((between r lx lz).idxOf x + 1)
      % (between r lx lz).length]'hpr ∈ between r lx lz := List.getElem_mem hpr
  have hIdxWs : Kepler.Text.TameSpine.indexf lx
      ((between s lx lz)[((between s lx lz).idxOf x + 1)
        % (between s lx lz).length]'hps) s
      = ((between s lx lz).idxOf x + 1) % (between s lx lz).length + 1 := by
    rw [← Kepler.Text.TameSpine.indexlBetwn hsnd hlx hlz hws,
      Kepler.Text.TameLp.idxOf_getElem hsndB hps]
  have hIdxWs' : Kepler.Text.Reduction5.indexf lx
      ((between s lx lz)[((between s lx lz).idxOf x + 1)
        % (between s lx lz).length]'hps) s
      = ((between s lx lz).idxOf x + 1) % (between s lx lz).length + 1 := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine lx
      ((between s lx lz)[((between s lx lz).idxOf x + 1)
        % (between s lx lz).length]'hps) s]
    exact hIdxWs
  have hIdxWsR : Kepler.Text.Reduction5.indexf lx
      ((between s lx lz)[((between s lx lz).idxOf x + 1)
        % (between s lx lz).length]'hps) r
      = ((between r lx lz).idxOf x + 1) % (between r lx lz).length + 1 := by
    have htr : Kepler.Text.Reduction5.indexf lx
        ((between s lx lz)[((between s lx lz).idxOf x + 1)
          % (between s lx lz).length]'hps) s
        = Kepler.Text.Reduction5.indexf lx
          ((between s lx lz)[((between s lx lz).idxOf x + 1)
            % (between s lx lz).length]'hps) r :=
      indexfCatBetwnSame hnd hy hz hyz hs hlx hws_s (by omega)
    rw [← htr]
    omega
  have hIdxWr : Kepler.Text.TameSpine.indexf lx
      ((between r lx lz)[((between r lx lz).idxOf x + 1)
        % (between r lx lz).length]'hpr) r
      = ((between r lx lz).idxOf x + 1) % (between r lx lz).length + 1 := by
    rw [← Kepler.Text.TameSpine.indexlBetwn hnd hlxr hlzr hwr,
      Kepler.Text.TameLp.idxOf_getElem hrndB hpr]
  have hIdxWr' : Kepler.Text.Reduction5.indexf lx
      ((between r lx lz)[((between r lx lz).idxOf x + 1)
        % (between r lx lz).length]'hpr) r
      = ((between r lx lz).idxOf x + 1) % (between r lx lz).length + 1 := by
    rw [Kepler.Text.Reduction3.indexf_eq_spine lx
      ((between r lx lz)[((between r lx lz).idxOf x + 1)
        % (between r lx lz).length]'hpr) r]
    exact hIdxWr
  have hws_r : (between s lx lz)[((between s lx lz).idxOf x + 1)
      % (between s lx lz).length]'hps ∈ r := hmemr _ hws_s
  have hwr_r : (between r lx lz)[((between r lx lz).idxOf x + 1)
      % (between r lx lz).length]'hpr ∈ r := Kepler.Graphs.inbetween_inset hwr
  have hEq : (between s lx lz)[((between s lx lz).idxOf x + 1)
      % (between s lx lz).length]'hps
      = (between r lx lz)[((between r lx lz).idxOf x + 1)
        % (between r lx lz).length]'hpr :=
    (Kepler.Text.Reduction4.indexfInj hlxr hws_r hwr_r).mp (by omega)
  rw [Kepler.Text.TameLp.nextEl_eq_getD hx,
    Kepler.Text.TameLp.getD_eq_getElem_of_lt hps,
    Kepler.Text.TameLp.nextEl_eq_getD hxr,
    Kepler.Text.TameLp.getD_eq_getElem_of_lt hpr]
  exact hEq

/-! ## §9 b2a（more_lemma1.hl:39 家族 + :592-:627）：
`normal_condition_last_parts`(:600) / `betwn_LAST_HD_parts`(:39) /
`LAST_betwn_LAST_HD_parts`(:90) / `next_betwn_LAST_HD_parts`(:250) /
`betwn_LAST_HD_parts_flatten`(:398)。

载体：`partsSpine`（TameList7）+ TameList5/6/9/10/11 parts 机器 + Leaf12 层
（`aqs_memFlattenBetwnSym(Case)` / `aqs_eq_last_next` / `aqs_uniqFlattenBetwn` /
`aqs_conditionLastParts` / `aqs_lastParts`）。`indexf` 全程 `TameSpine.indexf`
（Leaf12 层原生口径，免 R5 折桥）；`between`/`nextEl` 在 Dart 默认实例世界。
正向矛盾支的核心是**块偏移引理 L0**（part 块内元素在 `flatten` 中的下标 =
前置块长 + part 内下标），使 indexf 值全部落进 omega 线性算术。 -/

/-- **L0（b2a 块偏移引理）**：`r.flatten` 中 part `v` 块内元素 `a` 的下标 =
`v` 之前所有块的总长 + `v.idxOf a`。 -/
private theorem flattenIdxOfOffset {r : List (List Dart)} {v : List Dart}
    (hflat : r.flatten.Nodup) (hv : v ∈ r) (hall : ∀ q ∈ r, q ≠ [])
    {a : Dart} (ha : a ∈ v) :
    r.flatten.idxOf a
      = (r.take (r.idxOf v)).flatten.length + v.idxOf a := by
  have hip : r.idxOf v < r.length := List.idxOf_lt_length_iff.mpr hv
  have hrnd : r.Nodup := Kepler.Text.TameSpine.uniqFlatten (L := r) hflat hall
  have hdec : r.flatten = (r.take (r.idxOf v)).flatten ++ v
      ++ (r.drop (r.idxOf v + 1)).flatten := by
    have hr : r = r.take (r.idxOf v) ++ v :: r.drop (r.idxOf v + 1) := by
      calc r = r.take (r.idxOf v) ++ r.drop (r.idxOf v) := (List.take_append_drop _ _).symm
        _ = r.take (r.idxOf v) ++ (v :: r.drop (r.idxOf v + 1)) := by
              rw [List.drop_eq_getElem_cons hip, List.getElem_idxOf hip]
    have h := congrArg List.flatten hr
    simp only [List.flatten_append, List.flatten_cons] at h
    rw [h, List.append_assoc]
  have hfront : a ∉ (r.take (r.idxOf v)).flatten := by
    intro hcon
    obtain ⟨q, hq, haq⟩ := List.mem_flatten.mp hcon
    have hqr : q ∈ r := List.mem_of_mem_take hq
    have hlt := aqs_flatIdx_lt_of_partIdx_lt hflat hqr hv
      (aqs_idxOf_lt_of_mem_take hrnd hq) haq ha
    exact absurd hlt (Nat.lt_irrefl _)
  have htail : a ∉ (r.drop (r.idxOf v + 1)).flatten := by
    intro hcon
    obtain ⟨q, hq, haq⟩ := List.mem_flatten.mp hcon
    have hqr : q ∈ r := List.mem_of_mem_drop hq
    have hlt := aqs_flatIdx_lt_of_partIdx_lt hflat hv hqr
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (aqs_idxOf_ge_of_mem_drop hrnd hq)) ha haq
    exact absurd hlt (Nat.lt_irrefl _)
  rw [hdec, List.append_assoc]
  rw [List.idxOf_append (l₁ := (r.take (r.idxOf v)).flatten)
    (l₂ := v ++ (r.drop (r.idxOf v + 1)).flatten)]
  by_cases h1 : a ∈ (r.take (r.idxOf v)).flatten
  · exact absurd h1 hfront
  · rw [if_neg h1, List.idxOf_append (l₁ := v)
      (l₂ := (r.drop (r.idxOf v + 1)).flatten), if_pos ha]
    omega

/-- 同表双成员、`idxOf a ≤ idxOf b` ⇒ `indexf a b = idxOf b − idxOf a`
（不回卷段）。 -/
private theorem indexfOfIdxOfGe {s : List Dart} {a b : Dart} (ha : a ∈ s)
    (hb : b ∈ s) (h : s.idxOf a ≤ s.idxOf b) :
    Kepler.Text.TameSpine.indexf a b s = s.idxOf b - s.idxOf a := by
  have h1 : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr ha
  have h2 : s.idxOf b < s.length := List.idxOf_lt_length_iff.mpr hb
  unfold Kepler.Text.TameSpine.indexf
  rw [if_pos ⟨ha, hb⟩]
  have heq : s.idxOf b + (s.length - s.idxOf a)
      = s.idxOf b - s.idxOf a + s.length := by omega
  rw [heq, Nat.add_comm (s.idxOf b - s.idxOf a) s.length, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- 同表双成员、`idxOf b < idxOf a` ⇒ `indexf a b = |s| − (idxOf a − idxOf b)`
（回卷段）。 -/
private theorem indexfOfIdxOfLt {s : List Dart} {a b : Dart} (ha : a ∈ s)
    (hb : b ∈ s) (h : s.idxOf b < s.idxOf a) :
    Kepler.Text.TameSpine.indexf a b s = s.length - (s.idxOf a - s.idxOf b) := by
  have h1 : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr ha
  have h2 : s.idxOf b < s.length := List.idxOf_lt_length_iff.mpr hb
  unfold Kepler.Text.TameSpine.indexf
  rw [if_pos ⟨ha, hb⟩]
  have heq : s.idxOf b + (s.length - s.idxOf a)
      = s.length - (s.idxOf a - s.idxOf b) := by omega
  rw [heq]
  exact Nat.mod_eq_of_lt (by omega)

/-- **`HD_BETWN2` 的 BEq-泛型形**（DANGEYJ.hl:709 口径；§5 `hdBetwn2` 的
instBEqProd 世界孪生——§9 的 `between` 在 Dart 默认实例，不能直接消费 §5 的
`[DecidableEq]` 形）：弧非空时弧头 = 起点后继。证体沿 §5：`betwnTakeDrop`
双支 + §5 take/drop 头私件 + `nextEl_eq_getD`。 -/
private theorem hdBetwnG {f : List Dart} {u v : Dart} (hnd : f.Nodup)
    (hu : u ∈ f) (hv : v ∈ f) (hne : u ≠ v) (hne' : between f u v ≠ []) :
    (between f u v).head! = nextEl f u := by
  have hiu : f.idxOf u < f.length := List.idxOf_lt_length_iff.mpr hu
  have hiv : f.idxOf v < f.length := List.idxOf_lt_length_iff.mpr hv
  have hidxne : f.idxOf u ≠ f.idxOf v := fun he => hne ((List.idxOf_inj hu).mp he)
  have hpos : 0 < f.length := List.length_pos_of_mem hu
  rw [betwnTakeDrop hnd hv]
  rcases Nat.lt_or_ge (f.idxOf u) (f.idxOf v) with hlt | hge
  · have hk : 0 < f.idxOf v - (f.idxOf u + 1) := by
      by_contra hc
      have hm0 : f.idxOf v - (f.idxOf u + 1) = 0 := by omega
      apply hne'
      rw [betwnTakeDrop hnd hv, if_pos hlt, hm0]
      rfl
    rw [if_pos hlt,
      headBangTake (l := f.drop (f.idxOf u + 1))
        (n := f.idxOf v - (f.idxOf u + 1)) hk,
      headBangDrop (l := f) (n := f.idxOf u + 1) (by omega)]
    rw [Kepler.Text.TameLp.nextEl_eq_getD hu, Nat.mod_eq_of_lt (by omega)]
    exact (Kepler.Text.TameLp.getD_eq_getElem_of_lt (by omega) u).symm
  · have hlt2 : f.idxOf v < f.idxOf u := lt_of_le_of_ne hge (Ne.symm hidxne)
    by_cases hlast : f.idxOf u + 1 < f.length
    · have hne0 : f.drop (f.idxOf u + 1) ≠ [] := by
        intro h
        have hlen : List.length (f.drop (f.idxOf u + 1)) = 0 := by rw [h]; rfl
        rw [List.length_drop] at hlen
        omega
      rw [if_neg (Nat.not_lt.mpr hge), List.head!_append _ hne0, headBangDrop hlast,
        Kepler.Text.TameLp.nextEl_eq_getD hu, Nat.mod_eq_of_lt hlast]
      exact (Kepler.Text.TameLp.getD_eq_getElem_of_lt hlast u).symm
    · have hlastn : f.idxOf u + 1 = f.length := by omega
      have hdrop : f.drop (f.idxOf u + 1) = [] := by
        rw [hlastn]; exact List.drop_length
      have htake : f.take (f.idxOf v) ≠ [] := by
        intro h
        apply hne'
        rw [betwnTakeDrop hnd hv, if_neg (Nat.not_lt.mpr hge), hdrop, List.nil_append, h]
      have hi2pos : 0 < f.idxOf v := by
        rcases Nat.eq_zero_or_pos (f.idxOf v) with h | h
        · exfalso; apply htake; rw [h]; rfl
        · exact h
      rw [if_neg (Nat.not_lt.mpr hge), hdrop, List.nil_append,
        headBangTake (l := f) (n := f.idxOf v) hi2pos,
        Kepler.Text.TameLp.nextEl_eq_getD hu, hlastn, Nat.mod_self,
        Kepler.Text.TameLp.getD_eq_getElem_of_lt hpos u]
      cases f with
      | nil => exact absurd hu (by simp)
      | cons a t => rfl

/-- **HOL `normal_condition_last_parts`**（more_lemma1.hl:592）：
`MEM p (parts L r) ∧ MEM d p ∧ good_list L ∧ normal_list L N ∧ MEM r N ∧
is_edge_nondegenerate (hypermap_of_list L) ⇒
(¬(next_el r d = f_list L (e_list d)) ↔ d = LAST p)`。
证体：`d = LAST r` 支走 `aqs_lastParts` + `uniqSublistUnique`（p = 末 part）+
`normalListPartsNextLastNot`；其余支 = `aqs_conditionLastParts`（Leaf12T）。 -/
theorem normalConditionLastParts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} (hn : NormalListSpine hL N)
    (hnedg : (Kepler.Text.TameLp.hypermapOfList L hL).EdgeNondegenerate)
    {r : List Dart} (hr : r ∈ N) {p : List Dart} (hp : p ∈ partsSpine L r)
    {d : Dart} (hd : d ∈ p) :
    (¬(nextEl r d = fList L (eList d)) ↔ d = p.getLast!) := by
  obtain ⟨hrnd, hrne, -, -, -⟩ := partsUniqNonnil L hL hn hr hp
  by_cases hdl : d = r.getLast!
  · have hspne : partsSpine L r ≠ [] := partsNonnil L hrnd hrne
    have hall := partsAllNonnil L hrnd hrne
    have hsplast := aqs_lastParts L hL hn hr rfl
    have hspL : (partsSpine L r).getLast! ∈ partsSpine L r := aqs_getLastMem hspne
    have hlastInL : r.getLast! ∈ (partsSpine L r).getLast! := by
      have h2 := aqs_getLastMem (hall _ hspL)
      rwa [hsplast] at h2
    have hflatnd : (partsSpine L r).flatten.Nodup := by
      rw [partsFlatten L hrnd hrne]
      exact hrnd
    have hpe : (partsSpine L r).getLast! = p :=
      Kepler.Text.TameSpine.uniqSublistUnique (partsSpine L r) hflatnd
        ((partsSpine L r).getLast!) hspL p hp ⟨r.getLast!, hlastInL, hdl ▸ hd⟩
    constructor
    · intro _
      rw [← hpe, hsplast]
      exact hdl
    · intro hdpe
      rw [hdpe]
      exact normalListPartsNextLastNot L hL hn hnedg hr hp
  · exact aqs_conditionLastParts L hrnd hrne hp hd hdl

/-- **py 支矛盾**（`:39` 正向）：`x ∈ py ∩ B_r` 且 `x ≠ py.getLast!` 不可能。
块偏移 L0 把 `indexf py.last x r` 展开为 `|r|−|py|+1` 以上（F1），而
`indexf py.last pz.head! r ≤ |r|−|py|`（F2），与弧内 indexf 界冲突。 -/
private theorem notMemPyOfMemBetwn {r : List Dart} {sp : List (List Dart)}
    {py pz : List Dart} {x : Dart} (hrnd : r.Nodup) (hflr : sp.flatten = r)
    (hall : ∀ q ∈ sp, q ≠ [])
    (hpy : py ∈ sp) (hpz : pz ∈ sp) (hpynd : py.Nodup) (hpne : py ≠ [])
    (hpznd : pz.Nodup) (hpzne : pz ≠ [])
    (hlastmem : py.getLast! ∈ py) (hheadmem : pz.head! ∈ pz)
    (hllr : py.getLast! ∈ r) (hzhr : pz.head! ∈ r)
    (hlastne : py.getLast! ≠ pz.head!) (hpypz : py ≠ pz)
    (hxpy : x ∈ py) (hxn : x ≠ py.getLast!)
    (hx : x ∈ between r py.getLast! pz.head!) : False := by
  have hflatnd : sp.flatten.Nodup := by rw [hflr]; exact hrnd
  have hxr : x ∈ r := hflr ▸ List.mem_flatten.mpr ⟨py, hpy, hxpy⟩
  set T1 := (sp.take (sp.idxOf pz)).flatten.length with hT1
  set T2 := (sp.take (sp.idxOf py)).flatten.length with hT2
  have hl0l : r.idxOf py.getLast! = T2 + py.idxOf py.getLast! := by
    rw [← hflr]; exact flattenIdxOfOffset hflatnd hpy hall hlastmem
  have hl0x : r.idxOf x = T2 + py.idxOf x := by
    rw [← hflr]; exact flattenIdxOfOffset hflatnd hpy hall hxpy
  have hl0h : r.idxOf pz.head! = T1 + pz.idxOf pz.head! := by
    rw [← hflr]; exact flattenIdxOfOffset hflatnd hpz hall hheadmem
  have hl0zl : r.idxOf pz.getLast! = T1 + pz.idxOf pz.getLast! := by
    rw [← hflr]; exact flattenIdxOfOffset hflatnd hpz hall (aqs_getLastMem hpzne)
  have hel : py.idxOf py.getLast! = py.length - 1 := aqs_idxOfGetLast hpynd hpne
  have heh : pz.idxOf pz.head! = 0 := aqs_idxOfHead pz
  have hezl : pz.idxOf pz.getLast! = pz.length - 1 := aqs_idxOfGetLast hpznd hpzne
  have hlx : r.idxOf py.getLast! < r.length := List.idxOf_lt_length_iff.mpr hllr
  have hlb : r.idxOf pz.getLast! < r.length :=
    List.idxOf_lt_length_iff.mpr (hflr ▸ List.mem_flatten.mpr ⟨pz, hpz, aqs_getLastMem hpzne⟩)
  have hzx : T1 + pz.length ≤ r.length := by
    rw [hezl] at hl0zl
    omega
  have hxidxlt : py.idxOf x < py.length - 1 := by
    have h1 : py.idxOf x < py.length := List.idxOf_lt_length_iff.mpr hxpy
    have h2 : py.idxOf x ≠ py.length - 1 := by
      intro he
      apply hxn
      exact (List.idxOf_inj hxpy).mp (by rw [he, ← hel])
    omega
  obtain ⟨hposx, hltx⟩ :=
    (Kepler.Text.TameSpine.indexfBetwnEq hlastne hrnd hllr hzhr).mp hx
  have hF1 : r.length - py.length + 1 ≤ Kepler.Text.TameSpine.indexf py.getLast! x r := by
    have hord : r.idxOf x < r.idxOf py.getLast! := by
      rw [hl0x, hl0l, hel]
      omega
    have hval := indexfOfIdxOfLt hllr hxr hord
    rw [hl0x, hl0l, hel] at hval
    rw [hval]
    omega
  have hF2 : Kepler.Text.TameSpine.indexf py.getLast! pz.head! r
      ≤ r.length - py.length := by
    rcases Nat.lt_or_ge (sp.idxOf py) (sp.idxOf pz) with hlt | hge
    · have hordh : r.idxOf py.getLast! < r.idxOf pz.head! := by
        rw [← hflr]
        exact aqs_flatIdx_lt_of_partIdx_lt hflatnd hpy hpz hlt hlastmem hheadmem
      have hval := indexfOfIdxOfGe hllr hzhr (le_of_lt hordh)
      rw [hl0l, hl0h, hel, heh] at hval
      rw [hval]
      have hpl : 1 ≤ pz.length := List.length_pos_of_ne_nil hpzne
      omega
    · have hlt2 : sp.idxOf pz < sp.idxOf py := by
        rcases Nat.lt_or_ge (sp.idxOf pz) (sp.idxOf py) with h | h
        · exact h
        · exact absurd ((List.idxOf_inj hpz).mp (le_antisymm hge h)) (fun hc => hpypz hc.symm)
      have hordh : r.idxOf pz.head! < r.idxOf py.getLast! := by
        rw [← hflr]
        exact aqs_flatIdx_lt_of_partIdx_lt hflatnd hpz hpy hlt2 hheadmem hlastmem
      have hT12 : T1 + pz.length ≤ T2 := by
        have hord := aqs_flatIdx_lt_of_partIdx_lt hflatnd hpz hpy hlt2
          (aqs_getLastMem hpzne) (aqs_headMem hpne)
        rw [hflr] at hord
        have hh : r.idxOf py.head! = T2 := by
          have h := flattenIdxOfOffset hflatnd hpy hall (aqs_headMem hpne)
          rw [hflr] at h
          rw [h, aqs_idxOfHead py, Nat.add_zero]
        rw [hl0zl, hezl, hh] at hord
        omega
      have hval := indexfOfIdxOfLt hllr hzhr hordh
      rw [hl0l, hl0h, hel, heh] at hval
      rw [hval]
      omega
  omega

/-- **pz 支矛盾**（`:39` 正向，与 py 支镜像）：`x ∈ pz ∩ B_r` 且
`x ≠ pz.head!` 不可能（`indexf` 差 = `pz.idxOf x ≥ 1`）。 -/
private theorem notMemPzOfMemBetwn {r : List Dart} {sp : List (List Dart)}
    {py pz : List Dart} {x : Dart} (hrnd : r.Nodup) (hflr : sp.flatten = r)
    (hall : ∀ q ∈ sp, q ≠ [])
    (hpy : py ∈ sp) (hpz : pz ∈ sp) (hpynd : py.Nodup) (hpne : py ≠ [])
    (hpznd : pz.Nodup) (hpzne : pz ≠ [])
    (hlastmem : py.getLast! ∈ py) (hheadmem : pz.head! ∈ pz)
    (hllr : py.getLast! ∈ r) (hzhr : pz.head! ∈ r)
    (hlastne : py.getLast! ≠ pz.head!) (hpypz : py ≠ pz)
    (hxpz : x ∈ pz) (hxn : x ≠ pz.head!)
    (hx : x ∈ between r py.getLast! pz.head!) : False := by
  have hflatnd : sp.flatten.Nodup := by rw [hflr]; exact hrnd
  have hxr : x ∈ r := hflr ▸ List.mem_flatten.mpr ⟨pz, hpz, hxpz⟩
  set T1 := (sp.take (sp.idxOf pz)).flatten.length with hT1
  set T2 := (sp.take (sp.idxOf py)).flatten.length with hT2
  have hl0l : r.idxOf py.getLast! = T2 + py.idxOf py.getLast! := by
    rw [← hflr]; exact flattenIdxOfOffset hflatnd hpy hall hlastmem
  have hl0x : r.idxOf x = T1 + pz.idxOf x := by
    rw [← hflr]; exact flattenIdxOfOffset hflatnd hpz hall hxpz
  have hl0h : r.idxOf pz.head! = T1 + pz.idxOf pz.head! := by
    rw [← hflr]; exact flattenIdxOfOffset hflatnd hpz hall hheadmem
  have hel : py.idxOf py.getLast! = py.length - 1 := aqs_idxOfGetLast hpynd hpne
  have heh : pz.idxOf pz.head! = 0 := aqs_idxOfHead pz
  have hxidxpos : 1 ≤ pz.idxOf x := by
    rcases Nat.eq_zero_or_pos (pz.idxOf x) with h | h
    · exfalso
      apply hxn
      exact (List.idxOf_inj hxpz).mp (by rw [h, aqs_idxOfHead pz])
    · exact h
  obtain ⟨hposx, hltx⟩ :=
    (Kepler.Text.TameSpine.indexfBetwnEq hlastne hrnd hllr hzhr).mp hx
  rcases Nat.lt_or_ge (sp.idxOf py) (sp.idxOf pz) with hlt | hge
  · have hordh : r.idxOf py.getLast! < r.idxOf pz.head! := by
      rw [← hflr]
      exact aqs_flatIdx_lt_of_partIdx_lt hflatnd hpy hpz hlt hlastmem hheadmem
    have hTyt : T2 + py.length ≤ T1 := by
      have hord := aqs_flatIdx_lt_of_partIdx_lt hflatnd hpy hpz hlt
        hlastmem hheadmem
      rw [hflr] at hord
      have hh : r.idxOf pz.head! = T1 := by
        rw [hl0h, heh, Nat.add_zero]
      rw [hl0l, hel, hh] at hord
      omega
    have hordx : r.idxOf py.getLast! < r.idxOf x := by
      rw [hl0l, hl0x, hel]
      omega
    have hval := indexfOfIdxOfGe hllr hxr (le_of_lt hordx)
    rw [hl0l, hl0x, hel] at hval
    have hD := indexfOfIdxOfGe hllr hzhr (le_of_lt hordh)
    rw [hl0l, hl0h, hel, heh] at hD
    rw [hval, hD] at hltx
    omega
  · have hlt2 : sp.idxOf pz < sp.idxOf py := by
      rcases Nat.lt_or_ge (sp.idxOf pz) (sp.idxOf py) with h | h
      · exact h
      · exact absurd ((List.idxOf_inj hpz).mp (le_antisymm hge h)) (fun hc => hpypz hc.symm)
    have hordh : r.idxOf pz.head! < r.idxOf py.getLast! := by
      rw [← hflr]
      exact aqs_flatIdx_lt_of_partIdx_lt hflatnd hpz hpy hlt2 hheadmem hlastmem
    have hTty : T1 + pz.length ≤ T2 := by
      have hord := aqs_flatIdx_lt_of_partIdx_lt hflatnd hpz hpy hlt2
        (aqs_getLastMem hpzne) (aqs_headMem hpne)
      rw [hflr] at hord
      have hh : r.idxOf py.head! = T2 := by
        have h := flattenIdxOfOffset hflatnd hpy hall (aqs_headMem hpne)
        rw [hflr] at h
        rw [h, aqs_idxOfHead py, Nat.add_zero]
      have hl0zl : r.idxOf pz.getLast! = T1 + pz.idxOf pz.getLast! := by
        rw [← hflr]
        exact flattenIdxOfOffset hflatnd hpz hall (aqs_getLastMem hpzne)
      have hezl : pz.idxOf pz.getLast! = pz.length - 1 := aqs_idxOfGetLast hpznd hpzne
      rw [hl0zl, hezl, hh] at hord
      omega
    have hordx : r.idxOf x < r.idxOf py.getLast! := by
      have h2 : pz.idxOf x < pz.length := List.idxOf_lt_length_iff.mpr hxpz
      rw [hl0x, hl0l, hel]
      omega
    have hval := indexfOfIdxOfLt hllr hxr hordx
    rw [hl0l, hl0x, hel] at hval
    have hD := indexfOfIdxOfLt hllr hzhr hordh
    rw [hl0l, hl0h, hel, heh] at hD
    rw [hval, hD] at hltx
    omega


/-- **HOL `betwn_LAST_HD_parts`**（more_lemma1.hl:39）：
`s = parts L r ∧ py,pz ∈ s ∧ y∈py ∧ z∈pz ∧ FST y ≠ FST z ⇒
(∀x, x∈betwn r (LAST py) (HD pz) ↔ x∈flatten (betwn s py pz))`。
反向 = `aqs_memFlattenBetwnSym`；正向三岐（`aqs_memFlattenBetwnSymCase`）：
中间支直落，py/pz 支由块偏移 + indexf 界矛盾（`notMemPy/PzOfMemBetwn`）；
空支由 `betwnNil` + `fListQuotientAlt` 双向传播。 -/
theorem memBetwnLastHdParts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} (hn : NormalListSpine hL N) {r : List Dart} (hr : r ∈ N)
    {sp : List (List Dart)} (hsp : partsSpine L r = sp)
    (hunq : (sp.map (fun q => q.head!.1)).Nodup)
    {py pz : List Dart} (hpy : py ∈ sp) (hpz : pz ∈ sp)
    {y z : Dart} (hy : y ∈ py) (hz : z ∈ pz) (hyz : y.1 ≠ z.1) :
    ∀ x, x ∈ between r py.getLast! pz.head! ↔ x ∈ (between sp py pz).flatten := by
  obtain ⟨hrnd, hrne, hpynd, hpne, hysub⟩ := partsUniqNonnil L hL hn hr (hsp ▸ hpy)
  obtain ⟨-, -, hpznd, hpzne, hzsub⟩ := partsUniqNonnil L hL hn hr (hsp ▸ hpz)
  have hflr : sp.flatten = r := by rw [← hsp]; exact partsFlatten L hrnd hrne
  have hflatnd' : sp.flatten.Nodup := by rw [hflr]; exact hrnd
  have hspnd : sp.Nodup := by rw [← hsp]; exact uniqParts L hrnd hrne
  have hall : ∀ q ∈ sp, q ≠ [] := by rw [← hsp]; exact partsAllNonnil L hrnd hrne
  have hlastmem : py.getLast! ∈ py := aqs_getLastMem hpne
  have hheadmem : pz.head! ∈ pz := aqs_headMem hpzne
  have e1 : y.1 = py.head!.1 := partsFst L hL hn hr (hsp ▸ hpy) hy
  have e2 : py.getLast!.1 = py.head!.1 := partsFst L hL hn hr (hsp ▸ hpy) hlastmem
  have hfyl : y.1 = py.getLast!.1 := e1.trans e2.symm
  have hfz : z.1 = pz.head!.1 := partsFst L hL hn hr (hsp ▸ hpz) hz
  have hlastne : py.getLast! ≠ pz.head! := by
    intro hcon
    apply hyz
    rw [hfyl, hfz, hcon]
  have hpypz : py ≠ pz := by
    intro hcon
    apply hyz
    rw [hcon] at e1
    rw [e1, hfz]
  have hllr : py.getLast! ∈ r := hflr ▸ List.mem_flatten.mpr ⟨py, hpy, hlastmem⟩
  have hzhr : pz.head! ∈ r := hflr ▸ List.mem_flatten.mpr ⟨pz, hpz, hheadmem⟩
  by_cases hB : between r py.getLast! pz.head! = []
  · -- 空支：两侧同为空
    have hBsp : between sp py pz = [] := by
      by_contra hc
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hc
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (hall w (Kepler.Graphs.inbetween_inset hw))
      have hwf : v ∈ (between sp py pz).flatten := List.mem_flatten.mpr ⟨w, hw, hv⟩
      have hwr : v ∈ between r py.getLast! pz.head! := by
        have h := aqs_memFlattenBetwnSym (r := sp) (v := py) (v1 := pz) (d := v)
          (y := py.getLast!) (z := pz.head!) hflatnd' hwf hlastmem hheadmem
          hpypz hpy hpz hall
        rwa [hflr] at h
      rw [hB] at hwr
      exact absurd hwr (by simp)
    intro x
    constructor
    · intro hx
      rw [hB] at hx
      exact absurd hx (by simp)
    · intro hx
      rw [hBsp] at hx
      simp at hx
  · intro x
    constructor
    · intro hx
      have hxmem : x ∈ r := Kepler.Graphs.inbetween_inset hx
      obtain ⟨p, hp, hxp⟩ := partsMemExists L hrnd hxmem
      have htrich := aqs_memFlattenBetwnSymCase (r := sp) (v := py) (v1 := pz)
        (d := x) (y := py.getLast!) (z := pz.head!) hflatnd' hlastmem hheadmem
        hpypz hpy hpz hall (by rw [hflr]; exact hx)
      rcases htrich with hcpy | hcout | hcpz
      · have hxn : x ≠ py.getLast! := by
          intro hc
          have hIb :=
            (Kepler.Text.TameSpine.indexfBetwnEq hlastne hrnd hllr hzhr).mp hx
          rw [hc, Kepler.Text.TameSpine.indexfRefl hllr] at hIb
          exact absurd hIb.1 (by omega)
        exact False.elim (notMemPyOfMemBetwn hrnd hflr hall hpy hpz hpynd hpne
          hpznd hpzne hlastmem hheadmem hllr hzhr hlastne hpypz hcpy hxn hx)
      · exact hcout
      · have hxn : x ≠ pz.head! := by
          intro hc
          have hIb :=
            (Kepler.Text.TameSpine.indexfBetwnEq hlastne hrnd hllr hzhr).mp hx
          rw [hc] at hIb
          exact absurd hIb.2 (by omega)
        exact False.elim (notMemPzOfMemBetwn hrnd hflr hall hpy hpz hpynd hpne
          hpznd hpzne hlastmem hheadmem hllr hzhr hlastne hpypz hcpz hxn hx)
    · intro hx
      have h := aqs_memFlattenBetwnSym (r := sp) (v := py) (v1 := pz) (d := x)
        (y := py.getLast!) (z := pz.head!) hflatnd' hx hlastmem hheadmem
        hpypz hpy hpz hall
      rwa [hflr] at h

/-- `0 < n ≤ l.length ⇒ (l.take n).getLast! = l[n−1]`。 -/
private theorem takeGetLast {α : Type*} [Inhabited α] {l : List α} {n : ℕ}
    (hn : 0 < n) (hlt : n ≤ l.length) :
    (l.take n).getLast! = l[n - 1]'(by omega) := by
  have hlen : (l.take n).length = n := by
    rw [List.length_take, Nat.min_eq_left hlt]
  have hb : 0 < (l.take n).length := by
    rw [hlen]
    exact hn
  have hne : l.take n ≠ [] := by
    intro h
    rw [h] at hb
    simp at hb
  rw [getLastBangEqGetLast hne, List.getLast_eq_getElem hne]
  refine (getElemEqOfEqIdx (l := l.take n) (by rw [hlen]) (by omega)
    (by omega)).trans ?_
  exact List.getElem_take

/-- **弧尾件的 sp-后继 = 弧终点**：`q = (betwn sp py pz).getLast! ⇒ nextEl sp q = pz`
（弧非空、`py ≠ pz`）。`betwnTakeDrop` 双形四子支抽取 `q` 的 sp 下标：
非回卷 / 回卷 take 非空 —— `idxOf q + 1 = idxOf pz`；回卷 take 空（`pz = sp` 头元）
—— `q = sp 末元`。 -/
private theorem arcLastNext {sp : List (List Dart)} {py pz q : List Dart}
    (hspnd : sp.Nodup) (hpy : py ∈ sp) (hpz : pz ∈ sp) (hpyz : py ≠ pz)
    (hne : between sp py pz ≠ []) (hq : q = (between sp py pz).getLast!) :
    nextEl sp q = pz := by
  subst hq
  have hipy : sp.idxOf py < sp.length := List.idxOf_lt_length_iff.mpr hpy
  have hipz : sp.idxOf pz < sp.length := List.idxOf_lt_length_iff.mpr hpz
  have hidxne : sp.idxOf py ≠ sp.idxOf pz := fun he => hpyz ((List.idxOf_inj hpy).mp he)
  have hqidx : sp.idxOf (between sp py pz).getLast! + 1 = sp.idxOf pz
      ∨ (sp.idxOf (between sp py pz).getLast! = sp.length - 1 ∧ sp.idxOf pz = 0) := by
    rw [betwnTakeDrop hspnd hpz]
    rcases Nat.lt_or_ge (sp.idxOf py) (sp.idxOf pz) with hlt | hge
    · rw [if_pos hlt]
      have hm : 0 < sp.idxOf pz - (sp.idxOf py + 1) := by
        by_contra hc
        have h0 : sp.idxOf pz - (sp.idxOf py + 1) = 0 := by omega
        apply hne
        rw [betwnTakeDrop hspnd hpz, if_pos hlt, h0]
        rfl
      have hml : sp.idxOf pz - (sp.idxOf py + 1)
          ≤ (sp.drop (sp.idxOf py + 1)).length := by
        rw [List.length_drop]
        omega
      left
      rw [takeGetLast (l := sp.drop (sp.idxOf py + 1)) (n := sp.idxOf pz - (sp.idxOf py + 1)) hm hml, List.getElem_drop,
        Kepler.Text.TameLp.idxOf_getElem hspnd (by omega)]
      omega
    · rw [if_neg (Nat.not_lt.mpr hge)]
      by_cases htake : sp.take (sp.idxOf pz) = []
      · right
        have hj0 : sp.idxOf pz = 0 := by
          rcases List.take_eq_nil_iff.mp htake with h | h
          · exact h
          · exact absurd h (by intro hh; rw [hh] at hpz; simp at hpz)
        have hdne : sp.drop (sp.idxOf py + 1) ≠ [] := by
          intro h
          apply hne
          rw [betwnTakeDrop hspnd hpz, if_neg (Nat.not_lt.mpr hge), htake, h]
          rfl
        have hsne : sp ≠ [] := fun h => by rw [h] at hpz; simp at hpz
        have hone : (sp.drop (sp.idxOf py + 1) ++ sp.take (sp.idxOf pz)).getLast!
            = (sp.drop (sp.idxOf py + 1)).getLast! := by
          rw [htake, List.append_nil]
        have hgl : sp.idxOf (sp.drop (sp.idxOf py + 1)).getLast! = sp.length - 1 := by
          have hmem : (sp.drop (sp.idxOf py + 1)).getLast! ∈ sp.drop (sp.idxOf py + 1) :=
            aqs_getLastMem hdne
          have hnd : (sp.drop (sp.idxOf py + 1)).Nodup := uniqDrop hspnd
          have h1 : sp.idxOf (sp.drop (sp.idxOf py + 1)).getLast!
              = (sp.idxOf py + 1)
                + (sp.drop (sp.idxOf py + 1)).idxOf
                    (sp.drop (sp.idxOf py + 1)).getLast! :=
            aqs_idxOf_mem_drop_eq hspnd hmem
          have h2 : (sp.drop (sp.idxOf py + 1)).idxOf
              (sp.drop (sp.idxOf py + 1)).getLast!
              = (sp.drop (sp.idxOf py + 1)).length - 1 :=
            aqs_idxOfGetLast hnd hdne
          have hdlen : (sp.drop (sp.idxOf py + 1)).length
              = sp.length - (sp.idxOf py + 1) := List.length_drop
          have hdpos : 0 < (sp.drop (sp.idxOf py + 1)).length :=
            List.length_pos_of_ne_nil hdne
          rw [hdlen] at hdpos
          rw [h1, h2, hdlen]
          omega
        rw [hone, hgl]
        exact ⟨rfl, hj0⟩
      · left
        have hane : sp.drop (sp.idxOf py + 1) ++ sp.take (sp.idxOf pz) ≠ [] := by
          intro h
          exact htake (List.append_eq_nil_iff.mp h).2
        have hgle : (sp.drop (sp.idxOf py + 1) ++ sp.take (sp.idxOf pz)).getLast!
            = (sp.take (sp.idxOf pz)).getLast! := by
          rw [getLastBangEqGetLast hane, getLastBangEqGetLast htake,
            List.getLast_append_of_ne_nil hane htake]
        have hjpos : 0 < sp.idxOf pz := by
          rcases Nat.eq_zero_or_pos (sp.idxOf pz) with h0 | h
          · exact absurd (by rw [h0]; rfl : sp.take (sp.idxOf pz) = []) htake
          · exact h
        rw [hgle, takeGetLast (l := sp) (n := sp.idxOf pz) hjpos (le_of_lt hipz),
          Kepler.Text.TameLp.idxOf_getElem hspnd (by omega)]
        omega
  have hqmem : (between sp py pz).getLast! ∈ sp :=
    Kepler.Graphs.inbetween_inset (aqs_getLastMem hne)
  have hpos : 0 < sp.length := List.length_pos_of_mem hpz
  rcases hqidx with h | ⟨h1, h2⟩
  · have h3 : (sp.idxOf (between sp py pz).getLast! + 1) % sp.length
        = sp.idxOf pz := by
      rw [h, Nat.mod_eq_of_lt hipz]
    rw [Kepler.Text.TameLp.nextEl_eq_getD hqmem, h3,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt hipz]
    exact Kepler.Text.TameLp.getElem_idxOf hpz
  · have h3 : (sp.idxOf (between sp py pz).getLast! + 1) % sp.length = 0 := by
      rw [h1, show sp.length - 1 + 1 = sp.length from by omega, Nat.mod_self]
    rw [Kepler.Text.TameLp.nextEl_eq_getD hqmem, h3,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt hpos]
    refine (getElemEqOfEqIdx (l := sp) h2.symm hpos hipz).trans ?_
    exact Kepler.Text.TameLp.getElem_idxOf hpz

/-- **HOL `LAST_betwn_LAST_HD_parts`**（more_lemma1.hl:90）：
同前件 ⇒ `LAST (betwn r (LAST py) (HD pz)) = LAST (flatten (betwn sp py pz))`。
`w := B_sp.getLast!.getLast!`：`nextEl r w = pz.head!`（`nextElFlattenLast` +
`arcLastNext`）⇒ `indexf py.last w r = D − 1`（`indexfAddLeft` 三角 + `nextElIndexf`）
⇒ `betwnGetLastOfIndexfSuccG` 收口；flatten 末元经 `lastFlatten2` 转移。 -/
theorem lastBetwnLastHdParts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} (hn : NormalListSpine hL N) {r : List Dart} (hr : r ∈ N)
    {sp : List (List Dart)} (hsp : partsSpine L r = sp)
    (hunq : (sp.map (fun q => q.head!.1)).Nodup)
    {py pz : List Dart} (hpy : py ∈ sp) (hpz : pz ∈ sp)
    {y z : Dart} (hy : y ∈ py) (hz : z ∈ pz) (hyz : y.1 ≠ z.1) :
    (between r py.getLast! pz.head!).getLast! = (between sp py pz).flatten.getLast! := by
  obtain ⟨hrnd, hrne, hpynd, hpne, -⟩ := partsUniqNonnil L hL hn hr (hsp ▸ hpy)
  obtain ⟨-, -, hpznd, hpzne, -⟩ := partsUniqNonnil L hL hn hr (hsp ▸ hpz)
  have hflr : sp.flatten = r := by rw [← hsp]; exact partsFlatten L hrnd hrne
  have hflatnd' : sp.flatten.Nodup := by rw [hflr]; exact hrnd
  have hspnd : sp.Nodup := by rw [← hsp]; exact uniqParts L hrnd hrne
  have hall : ∀ q ∈ sp, q ≠ [] := by rw [← hsp]; exact partsAllNonnil L hrnd hrne
  have hlastmem : py.getLast! ∈ py := aqs_getLastMem hpne
  have hheadmem : pz.head! ∈ pz := aqs_headMem hpzne
  have e1 : y.1 = py.head!.1 := partsFst L hL hn hr (hsp ▸ hpy) hy
  have e2 : py.getLast!.1 = py.head!.1 := partsFst L hL hn hr (hsp ▸ hpy) hlastmem
  have hfz : z.1 = pz.head!.1 := partsFst L hL hn hr (hsp ▸ hpz) hz
  have hlastne : py.getLast! ≠ pz.head! := by
    intro hcon
    apply hyz
    rw [hfz]
    exact e1.trans (e2.symm.trans (congrArg Prod.fst hcon))
  have hpypz : py ≠ pz := by
    intro hcon
    apply hyz
    rw [hfz]
    exact e1.trans (congrArg (fun q => q.head!.1) hcon)
  have hllr : py.getLast! ∈ r := hflr ▸ List.mem_flatten.mpr ⟨py, hpy, hlastmem⟩
  have hzhr : pz.head! ∈ r := hflr ▸ List.mem_flatten.mpr ⟨pz, hpz, hheadmem⟩
  by_cases hB : between r py.getLast! pz.head! = []
  · rw [hB]
    have hmemiff := memBetwnLastHdParts L hL hn hr hsp hunq hpy hpz hy hz hyz
    have hBsp : between sp py pz = [] := by
      by_contra hc
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hc
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (hall w (Kepler.Graphs.inbetween_inset hw))
      have hvf : v ∈ (between sp py pz).flatten := List.mem_flatten.mpr ⟨w, hw, hv⟩
      have hvr : v ∈ ([] : List Dart) := by
        rw [← hB]
        have h := aqs_memFlattenBetwnSym (r := sp) (v := py) (v1 := pz) (d := v)
          (y := py.getLast!) (z := pz.head!) hflatnd' hvf hlastmem hheadmem
          hpypz hpy hpz hall
        rwa [hflr] at h
      exact absurd hvr (by simp)
    rw [hBsp]
    rfl
  · have hmemiff := memBetwnLastHdParts L hL hn hr hsp hunq hpy hpz hy hz hyz
    have hBsp : between sp py pz ≠ [] := by
      intro hc
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hB
      have h2 : w ∈ (between sp py pz).flatten := (hmemiff w).mp hw
      rw [hc] at h2
      exact absurd h2 (by simp)
    set q := (between sp py pz).getLast! with hq
    have hqmem : q ∈ between sp py pz := aqs_getLastMem hBsp
    have hqsp : q ∈ sp := Kepler.Graphs.inbetween_inset hqmem
    have hqne : q ≠ [] := hall q hqsp
    have hwm : q.getLast! ∈ q := aqs_getLastMem hqne
    have hwmem : q.getLast! ∈ (between sp py pz).flatten :=
      List.mem_flatten.mpr ⟨q, hqmem, hwm⟩
    have hwr : q.getLast! ∈ between r py.getLast! pz.head! := (hmemiff _).mpr hwmem
    have hwrR : q.getLast! ∈ r := Kepler.Graphs.inbetween_inset hwr
    have hnext : nextEl r q.getLast! = pz.head! := by
      rw [← hflr]
      rw [nextElFlattenLast hflatnd' hall hqsp]
      rw [arcLastNext hspnd hpy hpz hpypz hBsp hq]
    obtain ⟨hposw, hltw⟩ :=
      (Kepler.Text.TameSpine.indexfBetwnEq hlastne hrnd hllr hzhr).mp hwr
    have hneidx : r.idxOf py.getLast! ≠ r.idxOf pz.head! := fun he =>
      hlastne ((List.idxOf_inj hllr).mp he)
    have hstep : Kepler.Text.TameSpine.indexf q.getLast! pz.head! r = 1 :=
      nextElIndexf hwrR hzhr hrnd hnext (by
        have h1 : r.idxOf py.getLast! < r.length := List.idxOf_lt_length_iff.mpr hllr
        have h2 : r.idxOf pz.head! < r.length := List.idxOf_lt_length_iff.mpr hzhr
        omega)
    have hadd := indexfAddLeft hllr hwrR hzhr (le_of_lt hltw)
    rw [hstep] at hadd
    have hidxq : Kepler.Text.TameSpine.indexf py.getLast! q.getLast! r
        = Kepler.Text.TameSpine.indexf py.getLast! pz.head! r - 1 := by
      omega
    have hfin : (between r py.getLast! pz.head!).getLast! = q.getLast! :=
      betwnGetLastOfIndexfSuccG hlastne hllr hzhr hwr hrnd hidxq
    have hflat : (between sp py pz).flatten.getLast! = q.getLast! := by
      have hFne : (between sp py pz).flatten ≠ [] := List.ne_nil_of_mem hwmem
      have hqne' : (between sp py pz).getLast hBsp ≠ [] := by
        rw [← getLastBangEqGetLast hBsp, ← hq]
        exact hall q hqsp
      have h1 := lastFlatten2 hBsp hqne' hFne
      have hqeq : (between sp py pz).getLast hBsp = q := by
        rw [hq, getLastBangEqGetLast hBsp]
      have h2 : ((between sp py pz).getLast hBsp).getLast! = q.getLast! :=
        congrArg (fun l => l.getLast!) hqeq
      rw [getLastBangEqGetLast hFne, h1, ← getLastBangEqGetLast hqne',
        h2, getLastBangEqGetLast hqne]
    rw [hfin, ← hflat]

/-- `x ∈ l.take n ⇒ (l.take n).idxOf x = l.idxOf x`（Nodup）。 -/
private theorem takeIdxOfEq {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {l : List α} {x : α} {n : ℕ} (hn : l.Nodup) (hx : x ∈ l.take n) :
    (l.take n).idxOf x = l.idxOf x := by
  have hi : (l.take n).idxOf x < (l.take n).length := List.idxOf_lt_length_iff.mpr hx
  have hj2 : (l.take n).idxOf x < l.length := by
    rw [List.length_take] at hi
    exact lt_of_lt_of_le hi (Nat.min_le_right _ _)
  have h2 : l[(l.take n).idxOf x] = x := by
    rw [← List.getElem_take]
    exact List.getElem_idxOf hi
  conv_rhs => rw [← h2]
  exact (Kepler.Text.TameLp.idxOf_getElem hn hj2).symm


/-- `l.take (i + k) = l.take i ++ (l.drop i).take k`。 -/
private theorem takeAdd {α : Type*} (l : List α) (i k : ℕ) :
    l.take (i + k) = l.take i ++ (l.drop i).take k := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, List.take_add_one, ih, List.take_add_one,
      List.append_assoc, List.getElem?_drop]

/-- `l.take (i + 1) = l.take i ++ [l[i]]`（`i < l.length`）。 -/
private theorem takeSuccGetElem {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  rfl

/-- `|flatten (l.take n)| ≤ |flatten l|`。 -/
private theorem flatLenTakeLe {α : Type*} (l : List (List α)) (n : ℕ) :
    (l.take n).flatten.length ≤ l.flatten.length := by
  conv_rhs => rw [← List.take_append_drop n l]
  rw [List.flatten_append, List.length_append]
  omega

/-- 前缀单调：`i ≤ j ⇒ |flatten (take i)| ≤ |flatten (take j)|`。 -/
private theorem takeFlatLenMono {α : Type*} {l : List (List α)} {i j : ℕ} (h : i ≤ j) :
    (l.take i).flatten.length ≤ (l.take j).flatten.length := by
  rw [← Kepler.Text.TameSpine.takeTake h]
  exact flatLenTakeLe (l.take j) i


/-! ## §9.5 b2a-3d 弧前缀块偏移（`:250` 主引理前置）。

编排者按车道冻结包 `DELIVERY-b2a3d-FROZEN2.md` 的 v3 源收口（执行 §2 五点修法表；
另修支 C `heq` 的假陈述——原式缺 `C` 项，改为直接向 omega 供给线性事实）。
-/

/-- **弧前缀块拼接恒等式**（`:250` 主引理）：`w ∈ B_sp.flatten` 在 `flatten`
中的位置 = 其 r-环内位置（`py.getLast!` 起算，减一）。三支各出
「r.idxOf 等式 ∧ 取向」（取向直供 `indexfOfIdxOfGe/Lt` 参数，避免 rw 参数内 omega）。 -/
private theorem arcPrefixIdx (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} (hn : NormalListSpine hL N) {r : List Dart} (hr : r ∈ N)
    {sp : List (List Dart)} (hsp : partsSpine L r = sp)
    {py pz : List Dart} (hpy : py ∈ sp) (hpz : pz ∈ sp)
    {y z : Dart} (hy : y ∈ py) (hz : z ∈ pz) (hyz : y.1 ≠ z.1)
    {w : Dart} (hw : w ∈ (between sp py pz).flatten) :
    (between sp py pz).flatten.idxOf w + 1
      = Kepler.Text.TameSpine.indexf py.getLast! w r := by
  obtain ⟨hrnd, hrne, hpynd, hpne, -⟩ := partsUniqNonnil L hL hn hr (hsp ▸ hpy)
  obtain ⟨-, -, hpznd, hpzne, -⟩ := partsUniqNonnil L hL hn hr (hsp ▸ hpz)
  have hflr : sp.flatten = r := by rw [← hsp]; exact partsFlatten L hrnd hrne
  have hflatnd : sp.flatten.Nodup := by rw [hflr]; exact hrnd
  have hspnd : sp.Nodup := by rw [← hsp]; exact uniqParts L hrnd hrne
  have hall : ∀ q ∈ sp, q ≠ [] := by rw [← hsp]; exact partsAllNonnil L hrnd hrne
  have hallB : ∀ q ∈ between sp py pz, q ≠ [] :=
    fun q hq => hall q (Kepler.Graphs.inbetween_inset hq)
  have e1 : y.1 = py.head!.1 := partsFst L hL hn hr (hsp ▸ hpy) hy
  have e2 : py.getLast!.1 = py.head!.1 :=
    partsFst L hL hn hr (hsp ▸ hpy) (aqs_getLastMem hpne)
  have hfz : z.1 = pz.head!.1 := partsFst L hL hn hr (hsp ▸ hpz) hz
  have hlastne : py.getLast! ≠ pz.head! := by
    intro hcon
    apply hyz
    rw [hfz]
    exact e1.trans (e2.symm.trans (congrArg Prod.fst hcon))
  have hpypz : py ≠ pz := by
    intro hcon
    apply hyz
    rw [hfz]
    exact e1.trans (congrArg (fun q => q.head!.1) hcon)
  have hidxne : sp.idxOf py ≠ sp.idxOf pz := fun he => hpypz ((List.idxOf_inj hpy).mp he)
  have hBnd : (between sp py pz).flatten.Nodup :=
    aqs_uniqFlattenBetwn hflatnd hpy hpz hpypz hall
  obtain ⟨p, hp, hwp⟩ := List.mem_flatten.mp hw
  have hpq : p ∈ sp := Kepler.Graphs.inbetween_inset hp
  have hwr : w ∈ r := hflr ▸ List.mem_flatten.mpr ⟨p, hpq, hwp⟩
  have hllr : py.getLast! ∈ r :=
    hflr ▸ List.mem_flatten.mpr ⟨py, hpy, aqs_getLastMem (hall py hpy)⟩
  have hppos : 0 < p.length := List.length_pos_of_ne_nil (hall p hpq)
  have hwpLen : p.idxOf w < p.length := List.idxOf_lt_length_iff.mpr hwp
  have hFidx : (between sp py pz).flatten.idxOf w
      = ((between sp py pz).take ((between sp py pz).idxOf p)).flatten.length + p.idxOf w :=
    flattenIdxOfOffset hBnd hp hallB hwp
  have hspidx : r.idxOf w = (sp.take (sp.idxOf p)).flatten.length + p.idxOf w := by
    rw [← hflr]
    exact flattenIdxOfOffset hflatnd hpq hall hwp
  have hpypos : 0 < py.length := List.length_pos_of_ne_nil hpne
  have hlastidx : r.idxOf py.getLast!
      = (sp.take (sp.idxOf py)).flatten.length + py.length - 1 := by
    rw [← hflr]
    rw [flattenIdxOfOffset hflatnd hpy hall (aqs_getLastMem (hall py hpy)),
      aqs_idxOfGetLast hpynd hpne]
    omega
  have hT1 : (sp.take (sp.idxOf py + 1)).flatten.length
      = (sp.take (sp.idxOf py)).flatten.length + py.length := by
    rw [takeSuccGetElem (List.idxOf_lt_length_iff.mpr hpy), List.flatten_append,
      List.length_append]
    simp
  rcases Nat.lt_or_ge (sp.idxOf py) (sp.idxOf pz) with hlt | hge
  · -- A：非回卷
    have hpB : p ∈ (sp.drop (sp.idxOf py + 1)).take
        (sp.idxOf pz - (sp.idxOf py + 1)) := by
      have h := hp
      rwa [betwnTakeDrop hspnd hpz, if_pos hlt] at h
    have hpdrop : p ∈ sp.drop (sp.idxOf py + 1) := List.mem_of_mem_take hpB
    have hk : sp.idxOf p = sp.idxOf py + 1 + (sp.drop (sp.idxOf py + 1)).idxOf p :=
      aqs_idxOf_mem_drop_eq hspnd hpdrop
    have hBp : (between sp py pz).idxOf p
        = (sp.drop (sp.idxOf py + 1)).idxOf p := by
      rw [betwnTakeDrop hspnd hpz, if_pos hlt]
      exact takeIdxOfEq (uniqDrop hspnd) hpB
    have hY : ((between sp py pz).take ((between sp py pz).idxOf p)).flatten.length
        = ((sp.drop (sp.idxOf py + 1)).take
            ((sp.drop (sp.idxOf py + 1)).idxOf p)).flatten.length := by
      rw [hBp, betwnTakeDrop hspnd hpz, if_pos hlt]
      rw [Kepler.Text.TameSpine.takeTake (by
        have h := List.idxOf_lt_length_iff.mpr hpB
        rw [List.length_take] at h
        have hidx : ((sp.drop (sp.idxOf py + 1)).take
            (sp.idxOf pz - (sp.idxOf py + 1))).idxOf p
            = (sp.drop (sp.idxOf py + 1)).idxOf p :=
          takeIdxOfEq (uniqDrop hspnd) hpB
        have hk2 : (sp.drop (sp.idxOf py + 1)).idxOf p
            < sp.idxOf pz - (sp.idxOf py + 1) := by
          rw [← hidx]
          exact lt_of_lt_of_le h (Nat.min_le_left _ _)
        omega)]
    have hTp : (sp.take (sp.idxOf p)).flatten.length
        = (sp.take (sp.idxOf py + 1)).flatten.length
          + ((between sp py pz).take ((between sp py pz).idxOf p)).flatten.length := by
      rw [hk, takeAdd, List.flatten_append, List.length_append, ← hY]
    set A := (sp.take (sp.idxOf py)).flatten.length with hA
    set B := py.length with hB
    set C := ((between sp py pz).take ((between sp py pz).idxOf p)).flatten.length with hC
    have hTp' : (sp.take (sp.idxOf p)).flatten.length = A + B + C := by
      rw [hTp, hT1]
    have heq : r.idxOf w = r.idxOf py.getLast! + C + p.idxOf w + 1 := by
      rw [hspidx, hlastidx, hTp']
      omega
    have hori : r.idxOf py.getLast! ≤ r.idxOf w := by
      rw [hspidx, hlastidx, hTp']
      omega
    rw [indexfOfIdxOfGe hllr hwr hori, hFidx]
    omega
  · by_cases hpd : p ∈ sp.drop (sp.idxOf py + 1)
    · -- B：回卷-drop
      have hk : sp.idxOf p = sp.idxOf py + 1 + (sp.drop (sp.idxOf py + 1)).idxOf p :=
        aqs_idxOf_mem_drop_eq hspnd hpd
      have hBp : (between sp py pz).idxOf p
          = (sp.drop (sp.idxOf py + 1)).idxOf p := by
        rw [betwnTakeDrop hspnd hpz, if_neg (Nat.not_lt.mpr hge), List.idxOf_append,
          if_pos hpd]
      have hY : ((between sp py pz).take ((between sp py pz).idxOf p)).flatten.length
          = ((sp.drop (sp.idxOf py + 1)).take
              ((sp.drop (sp.idxOf py + 1)).idxOf p)).flatten.length := by
        rw [hBp, betwnTakeDrop hspnd hpz, if_neg (Nat.not_lt.mpr hge)]
        rw [List.take_append]
        rw [show (sp.drop (sp.idxOf py + 1)).idxOf p
            - (sp.drop (sp.idxOf py + 1)).length = 0 from by
          have h := List.idxOf_lt_length_iff.mpr hpd
          omega]
        simp
      have hTp : (sp.take (sp.idxOf p)).flatten.length
          = (sp.take (sp.idxOf py + 1)).flatten.length
            + ((between sp py pz).take ((between sp py pz).idxOf p)).flatten.length := by
        rw [hk, takeAdd, List.flatten_append, List.length_append, ← hY]
      set A := (sp.take (sp.idxOf py)).flatten.length with hA
      set B := py.length with hB
      set C := ((between sp py pz).take ((between sp py pz).idxOf p)).flatten.length with hC
      have hTp' : (sp.take (sp.idxOf p)).flatten.length = A + B + C := by
        rw [hTp, hT1]
      have heq : r.idxOf w = r.idxOf py.getLast! + C + p.idxOf w + 1 := by
        rw [hspidx, hlastidx, hTp']
        omega
      have hori : r.idxOf py.getLast! ≤ r.idxOf w := by
        rw [hspidx, hlastidx, hTp']
        omega
      rw [indexfOfIdxOfGe hllr hwr hori, hFidx]
      omega
    · -- C：回卷-take
      have hpt : p ∈ sp.take (sp.idxOf pz) := by
        rcases List.mem_append.mp (show p ∈ sp.drop (sp.idxOf py + 1)
            ++ sp.take (sp.idxOf pz) from by
          have h := hp
          rwa [betwnTakeDrop hspnd hpz, if_neg (Nat.not_lt.mpr hge)] at h) with h | h
        · exact absurd h hpd
        · exact h
      have hk : sp.idxOf p = (sp.take (sp.idxOf pz)).idxOf p :=
        (takeIdxOfEq hspnd hpt).symm
      have hpi : sp.idxOf p < sp.idxOf py := by
        have h := List.idxOf_lt_length_iff.mpr hpt
        rw [List.length_take] at h
        rw [hk]
        have h1 : min (sp.idxOf pz) sp.length ≤ sp.idxOf pz := Nat.min_le_left _ _
        have h2 : sp.idxOf pz < sp.idxOf py := lt_of_le_of_ne hge (Ne.symm hidxne)
        omega
      have hBp : (between sp py pz).idxOf p
          = (sp.take (sp.idxOf pz)).idxOf p + (sp.drop (sp.idxOf py + 1)).length := by
        rw [betwnTakeDrop hspnd hpz, if_neg (Nat.not_lt.mpr hge), List.idxOf_append,
          if_neg hpd]
      have hY : ((between sp py pz).take ((between sp py pz).idxOf p)).flatten.length
          = (sp.drop (sp.idxOf py + 1)).flatten.length
            + (sp.take (sp.idxOf p)).flatten.length := by
        rw [hBp, betwnTakeDrop hspnd hpz, if_neg (Nat.not_lt.mpr hge)]
        rw [List.take_append]
        have hAn : (sp.drop (sp.idxOf py + 1)).take
            ((sp.take (sp.idxOf pz)).idxOf p
              + (sp.drop (sp.idxOf py + 1)).length)
            = sp.drop (sp.idxOf py + 1) :=
          List.take_of_length_le (by omega)
        rw [hAn]
        rw [show (sp.take (sp.idxOf pz)).idxOf p
            + (sp.drop (sp.idxOf py + 1)).length
            - (sp.drop (sp.idxOf py + 1)).length
            = (sp.take (sp.idxOf pz)).idxOf p from by
          have h := List.idxOf_lt_length_iff.mpr hpt
          rw [List.length_take] at h
          omega]
        rw [Kepler.Text.TameSpine.takeTake (by
          have h := List.idxOf_lt_length_iff.mpr hpt
          rw [List.length_take] at h
          omega)]
        rw [← hk, List.flatten_append, List.length_append]
      have hsp1 : r.length = (sp.take (sp.idxOf py + 1)).flatten.length
          + (sp.drop (sp.idxOf py + 1)).flatten.length := by
        rw [← hflr, ← List.length_append, ← List.flatten_append, List.take_append_drop]
      set A := (sp.take (sp.idxOf py)).flatten.length with hA
      set B := py.length with hB
      set C := (sp.drop (sp.idxOf py + 1)).flatten.length with hC
      have hA1 : (sp.take (sp.idxOf py + 1)).flatten.length = A + B := by
        rw [hT1]
      have hlen : r.length = A + B + C := by
        rw [hsp1, hA1]
      -- 取向：T_p < A+B（严格）
      have hmid : (sp.take (sp.idxOf p)).flatten.length + p.length
          ≤ (sp.take (sp.idxOf py)).flatten.length := by
        have h1 : (sp.take (sp.idxOf p + 1)).flatten.length
            = (sp.take (sp.idxOf p)).flatten.length + p.length := by
          rw [takeSuccGetElem (List.idxOf_lt_length_iff.mpr hpq), List.flatten_append,
            List.length_append]
          simp
        rw [← h1]
        exact takeFlatLenMono (Nat.succ_le_of_lt hpi)
      have hori : r.idxOf w < r.idxOf py.getLast! := by
        have hh : (sp.take (sp.idxOf p)).flatten.length + p.idxOf w
            < (sp.take (sp.idxOf py)).flatten.length := by
          omega
        rw [hspidx, hlastidx]
        omega
      rw [indexfOfIdxOfLt hllr hwr hori, hFidx]
      omega
end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.hdCat
#print axioms Kepler.Text.TameSpine.nextElInj
#print axioms Kepler.Text.TameSpine.eqHdLastBetwn
#print axioms Kepler.Text.TameSpine.memHdLastBetwn
#print axioms Kepler.Text.TameSpine.lastHdLastBetwn
#print axioms Kepler.Text.TameSpine.nextHdLastBetwn
#print axioms Kepler.Text.TameSpine.betwnCat
#print axioms Kepler.Text.TameSpine.hdBetwn2
#print axioms Kepler.Text.TameSpine.eqMemNextElLast
#print axioms Kepler.Text.TameSpine.nextElBetwnSame
#print axioms Kepler.Text.TameSpine.nextCatBetwnSamePower
#print axioms Kepler.Text.TameSpine.indexfCatBetwnSame
#print axioms Kepler.Text.TameSpine.indexfCatBetwnSame1
#print axioms Kepler.Text.TameSpine.memCatBetwnSame
#print axioms Kepler.Text.TameSpine.lastCatBetwnSame
#print axioms Kepler.Text.TameSpine.catBetwnSame
#print axioms Kepler.Text.TameSpine.normalConditionLastParts
#print axioms Kepler.Text.TameSpine.memBetwnLastHdParts
#print axioms Kepler.Text.TameSpine.lastBetwnLastHdParts
