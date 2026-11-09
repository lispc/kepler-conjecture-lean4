/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12G — AQ12 叶 W4a（decls 30–33，contour 四件）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:1387-:1508
  ┌──────────────────────────────────────────────────────────────┐
  │ decl 30 `contour_list_cat`     :1387（35）                     │
  │ decl 31 `next_el_EL`           :1422（10）                     │
  │ decl 32 `contour_betwn_loop`   :1432（32）                     │
  │ decl 33 `exists_conected_loop` :1464（45）                     │
  └──────────────────────────────────────────────────────────────┘
  （W4b = decls 27–29，:1141-:1386，另交；两段互不依赖。）

  ┌─ 路线（HOL 的 list/allP 展开 vs Lean 的 getElem 直算）──────────
  │ · decl 31：`nextEl r r[i] = r[i+1]` 用 `idxOf_getElem` + `nextEl` 的
  │   getD 分支（自建 `aqs_nextEl_eq_getElem_succ`）；HOL 的
  │   `index_el`/`EL_nth` 两条不需要。
  │ · decl 32：HOL 走 `LAST_EL`/`card_set_of_list_uniq`/
  │   `CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT` 三件（本树全零命中）；
  │   Lean 直接 `nextEl (betwn..) d = nextEl s d`（在库 `aq10_nextElBetwnSame`）
  │   ⇒ **不需要** card/LAST_EL 机器（清单 §2.2 的 3 条零命中从 W4 前置划掉）。
  │ · decl 30/33：`ContourListSpine`（`s[i]!` junk 形）逐 index 拆
  │   `getElem_append_left/right`；junction 用 `getLast`/`head` 两支。
  └────────────────────────────────────────────────────────────────

  ┌─ 跨车道协调（编排者 2026-11-09 指令）──────────────────────
  │ `HD_BETWN2`（DANGEYJ.hl:709）是 decl 33 junction 的必需件，本树零命中；
  │ AQ4 车道在飞（E1/E2/E3）未落任何 `aq4_` 声明。按「先报告、按条件槽落、
  │ 不许等、不许重造」：本文件自建**中立公开件 `aqs_hdBetwn2`**（DANGEYJ
  │ 原陈述、`aqs_` 前缀），**不建消费 AQ4 的槽**；AQ4 若需要可直接 import
  │ 本件（同一陈述只应有一份，后续禁止双造）。
  └────────────────────────────────────────────────────────────────

  载体：`List (ℕ × ℕ)`。纪律：零 sorry/admit/native_decide/axiom 声明；
  既有文件零触碰；主仓 tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12F
import Kepler.Text.TameSpine.JcajyduAqLeaf10
import Kepler.Text.TameSpine.TameList8
import Kepler.Text.TameSpine.TameList13
import Kepler.Text.TameSpine.TameList11
import Kepler.Text.TameSpine.JcajyduBetwnBase

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl listOfDarts)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (getD_eq_getElem_of_lt idxOf_getElem getElem_idxOf)

/-! ## §0 通用辅件 -/

private theorem aqs_getElemBang {l : List (ℕ × ℕ)} {i : ℕ} (hi : i < l.length) :
    l[i]! = l[i]'hi := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

private theorem aqs_headBang_zero {l : List (ℕ × ℕ)} (hl : l ≠ []) :
    l.head! = l[0]'(List.length_pos_of_ne_nil hl) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

private theorem aqs_getLastBang_last {l : List (ℕ × ℕ)} (hl : l ≠ []) :
    l.getLast! = l[l.length - 1]'(by
      have h := List.length_pos_of_ne_nil hl; omega) := by
  rw [getLast!EqGetLast hl, List.getLast_eq_getElem hl]

private theorem aqs_getElem_congr {α : Type*} {s : List α} {i j : ℕ} (h : i = j)
    (hi : i < s.length) (hj : j < s.length) : s[i]'hi = s[j]'hj := by
  cases h
  rfl

/-- `idxOf` 在 Nodup 表上单射到元素（本文件私件；与 Leaf12F 私件同证重推导）。 -/
private theorem aqs_idxOfInj {s : List (ℕ × ℕ)} (hnd : s.Nodup) {a b : ℕ × ℕ}
    (ha : a ∈ s) (hb : b ∈ s) (h : s.idxOf a = s.idxOf b) : a = b := by
  have hlt_a : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr ha
  have hlt_b : s.idxOf b < s.length := List.idxOf_lt_length_iff.mpr hb
  have e1 : s[s.idxOf a]? = some a := by
    rw [List.getElem?_eq_getElem hlt_a, List.getElem_idxOf hlt_a]
  have e2 : s[s.idxOf b]? = some b := by
    rw [List.getElem?_eq_getElem hlt_b, List.getElem_idxOf hlt_b]
  have h' : s[s.idxOf a]? = s[s.idxOf b]? := by rw [h]
  rw [e1, e2] at h'
  exact Option.some.inj h'

/-- `nextEl r a` 的 getElem 形（`idxOf a + 1 < |r|`；即 a 不是 LAST）。 -/
theorem aqs_nextEl_eq_getElem_succ {r : List (ℕ × ℕ)} (hr : r.Nodup) {a : ℕ × ℕ}
    (ha : a ∈ r) (h : r.idxOf a + 1 < r.length) : nextEl r a = r[r.idxOf a + 1] := by
  unfold Kepler.Assembly.nextEl
  rw [if_neg (by omega), getD_eq_getElem_of_lt h]

/-- **HOL `next_el_EL`**（AQ12.hl:1422-:1431）：`uniq r ∧ SUC i < sizel r ⇒
next_el r (EL i r) = EL (SUC i) r`。 -/
theorem aqs_nextElGetElem {r : List (ℕ × ℕ)} (hr : r.Nodup) {i : ℕ}
    (hi : i + 1 < r.length) : nextEl r r[i] = r[i + 1] := by
  have hi0 : i < r.length := by omega
  have hidx : r.idxOf r[i] = i := idxOf_getElem hr hi0
  have h := aqs_nextEl_eq_getElem_succ hr (List.getElem_mem hi0) (by rw [hidx]; exact hi)
  rw [h]
  exact aqs_getElem_congr (by omega) _ _

/-- `List.take m X` 的 head!（`m ≠ 0` 时取 `X.head!`）。 -/
private theorem aqs_headBang_take {α : Type*} [Inhabited α] {X : List α} {m : ℕ}
    (hm : m ≠ 0) : (X.take m).head! = X.head! := by
  cases X with
  | nil => simp
  | cons x xs =>
    cases m with
    | zero => exact absurd rfl hm
    | succ k => rw [List.take_succ_cons, List.head!_cons, List.head!_cons]

/-- 非空左段的拼接 head!（`List.head!_append` 的显式形，便于 rw）。 -/
private theorem aqs_headBang_append_of_ne {α : Type*} [Inhabited α] {s t : List α}
    (hs : s ≠ []) : (s ++ t).head! = s.head! :=
  List.head!_append t hs

/-- `List.drop k r` 的 head!（`k < |r|` 时取 `r[k]`）。 -/
private theorem aqs_headBang_drop {α : Type*} [Inhabited α] {r : List α} {k : ℕ}
    (hk : k < r.length) : (r.drop k).head! = r[k] := by
  rw [List.drop_eq_getElem_cons hk, List.head!_cons]

/-- **HOL `Dangeyj.HD_BETWN2`**（DANGEYJ.hl:709）：
`uniq r ∧ a,b ∈ r ∧ a≠b ∧ betwn 非空 ⇒ HD (betwn r a b) = next_el r a`。
（跨车道协调：AQ4 在飞未落 `aq4_` 声明，本件以中立 `aqs_` 公开件落地，
后续**禁止双造**。） -/
theorem aqs_hdBetwn2 {r : List (ℕ × ℕ)} {a b : ℕ × ℕ} (hr : r.Nodup) (ha : a ∈ r)
    (hb : b ∈ r) (hab : a ≠ b) (hne : between r a b ≠ []) :
    (between r a b).head! = nextEl r a := by
  have hia : r.idxOf a < r.length := List.idxOf_lt_length_iff.mpr ha
  have hib : r.idxOf b < r.length := List.idxOf_lt_length_iff.mpr hb
  have hiab : r.idxOf a ≠ r.idxOf b := fun h => hab (aqs_idxOfInj hr ha hb h)
  by_cases h1 : r.idxOf a < r.idxOf b
  · have hm : r.idxOf b - (r.idxOf a + 1) ≠ 0 := by
      intro h0
      apply hne
      rw [betwnTakeDrop hr hb, if_pos h1, List.take_eq_nil_iff]
      exact Or.inl h0
    rw [betwnTakeDrop hr hb, if_pos h1, aqs_headBang_take hm, aqs_headBang_drop (by omega)]
    exact (aqs_nextEl_eq_getElem_succ hr ha (by omega)).symm
  · rw [betwnTakeDrop hr hb, if_neg h1]
    by_cases h2 : r.idxOf a + 1 < r.length
    · have hhead : (r.drop (r.idxOf a + 1) ++ r.take (r.idxOf b)).head!
          = (r.drop (r.idxOf a + 1)).head! := by
        apply aqs_headBang_append_of_ne
        intro h
        rw [List.drop_eq_nil_iff] at h
        omega
      rw [hhead, aqs_headBang_drop h2]
      exact (aqs_nextEl_eq_getElem_succ hr ha h2).symm
    · -- a 是整体 LAST：nextEl 回卷到表头
      have hia_last : r.idxOf a = r.length - 1 := by omega
      have hdrop : r.drop (r.idxOf a + 1) = [] := by
        rw [List.drop_eq_nil_iff]
        omega
      have hb0 : r.idxOf b ≠ 0 := by
        intro h0
        apply hne
        rw [betwnTakeDrop hr hb, if_neg h1, hdrop, List.nil_append, List.take_eq_nil_iff]
        exact Or.inl h0
      rw [hdrop, List.nil_append, aqs_headBang_take hb0]
      unfold Kepler.Assembly.nextEl
      rw [if_pos hia_last]
      have hne_r : r ≠ [] := List.ne_nil_of_mem ha
      rw [show r.headD a = r.head! from by
        cases r with
        | nil => exact absurd rfl hne_r
        | cons x xs => rw [List.head!_cons]; rfl]

/-! ## §1 HOL AQ12.hl:1387 `contour_list_cat` -/

/-- `(s ++ r)` 在位置 `i` 的 getElem!（i 落在 s 内）。 -/
private theorem aqs_getElemBang_append_left {s r : List (ℕ × ℕ)} {i : ℕ}
    (hi : i < s.length) : (s ++ r)[i]! = s[i]! := by
  have hi' : i < (s ++ r).length := by rw [List.length_append]; omega
  rw [aqs_getElemBang hi', aqs_getElemBang hi, List.getElem_append_left hi]

/-- `(s ++ r)` 在位置 `i` 的 getElem!（i 落在 r 内，偏移 s.length）。 -/
private theorem aqs_getElemBang_append_right {s r : List (ℕ × ℕ)} {i : ℕ}
    (hi : i < r.length) : (s ++ r)[s.length + i]! = r[i]! := by
  have hi' : s.length + i < (s ++ r).length := by rw [List.length_append]; omega
  rw [aqs_getElemBang hi', aqs_getElemBang hi,
    List.getElem_append_right (show s.length ≤ s.length + i by omega)]
  exact aqs_getElem_congr (by omega) _ _

/-- 拼接表非空时 head! 取左段（左段非空）。 -/
private theorem aqs_headBang_append_eq {s r : List (ℕ × ℕ)} (hs : s ≠ []) :
    (s ++ r).head! = s.head! :=
  List.head!_append r hs

/-- **HOL `contour_list_cat`**（AQ12.hl:1387-:1421）：
`~s=[] ∧ ~r=[] ⇒ (contour_list L (s++r) ⇔ contour_list L s ∧
contour_list L r ∧ one_step_list L (LAST s) (HD r))`。 -/
theorem aqs_contourListCat {L : fgraph ℕ} {s r : List (ℕ × ℕ)}
    (hs : s ≠ []) (hr : r ≠ []) :
    ContourListSpine L (s ++ r) ↔
      ContourListSpine L s ∧ ContourListSpine L r ∧
        oneStepListSpine L s.getLast! r.head! := by
  have hs0 : 0 < s.length := List.length_pos_of_ne_nil hs
  have hr0 : 0 < r.length := List.length_pos_of_ne_nil hr
  have hlen : (s ++ r).length = s.length + r.length := List.length_append
  constructor
  · intro hc
    obtain ⟨hmem, hstep⟩ := hc
    refine ⟨⟨fun x hx => hmem x (List.mem_append.mpr (Or.inl hx)), ?_⟩,
      ⟨fun x hx => hmem x (List.mem_append.mpr (Or.inr hx)), ?_⟩, ?_⟩
    · intro i hi
      have hi' : i + 1 < (s ++ r).length := by rw [hlen]; omega
      rw [← aqs_getElemBang_append_left (show i < s.length by omega),
        ← aqs_getElemBang_append_left hi]
      exact hstep i hi'
    · intro i hi
      have hi' : s.length + i + 1 < (s ++ r).length := by rw [hlen]; omega
      rw [← aqs_getElemBang_append_right (show i < r.length by omega),
        ← aqs_getElemBang_append_right hi]
      exact hstep (s.length + i) hi'
    · have hk : s.length - 1 + 1 < (s ++ r).length := by rw [hlen]; omega
      have h := hstep (s.length - 1) hk
      have h1 : (s ++ r)[s.length - 1]! = s.getLast! := by
        rw [aqs_getElemBang_append_left (show s.length - 1 < s.length by omega),
          aqs_getElemBang (show s.length - 1 < s.length by omega)]
        exact (aqs_getLastBang_last hs).symm
      have h2 : (s ++ r)[s.length - 1 + 1]! = r.head! := by
        have e : (s ++ r)[s.length - 1 + 1]! = r[0]! := by
          rw [show s.length - 1 + 1 = s.length + 0 from by omega,
            aqs_getElemBang_append_right (show 0 < r.length by omega)]
        rw [e, aqs_getElemBang (show 0 < r.length by omega), ← aqs_headBang_zero hr]
      rwa [h1, h2] at h
  · rintro ⟨⟨hms, hsts⟩, ⟨hmr, hstr⟩, hjunc⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hms x h
      · exact hmr x h
    · intro i hi
      rcases lt_or_ge (i + 1) s.length with hlt | hge
      · have h := hsts i hlt
        rw [aqs_getElemBang_append_left (show i < s.length by omega),
          aqs_getElemBang_append_left hlt]
        exact h
      · rcases eq_or_lt_of_le hge with heq | hgt
        · -- junction：i = s.length - 1
          have hi_eq : i = s.length - 1 := by omega
          have h1 : (s ++ r)[i]! = s.getLast! := by
            subst hi_eq
            rw [aqs_getElemBang_append_left (show s.length - 1 < s.length by omega),
              aqs_getElemBang (show s.length - 1 < s.length by omega)]
            exact (aqs_getLastBang_last hs).symm
          have h2 : (s ++ r)[i + 1]! = r.head! := by
            subst hi_eq
            have e : (s ++ r)[s.length - 1 + 1]! = r[0]! := by
              rw [show s.length - 1 + 1 = s.length + 0 from by omega,
                aqs_getElemBang_append_right (show 0 < r.length by omega)]
            rw [e, aqs_getElemBang (show 0 < r.length by omega), ← aqs_headBang_zero hr]
          rw [h1, h2]
          exact hjunc
        · -- i 落在 r 内
          have hi' : i - s.length + 1 < r.length := by omega
          have h := hstr (i - s.length) hi'
          have h1 : (s ++ r)[i]! = r[i - s.length]! := by
            have h := aqs_getElemBang_append_right (s := s) (r := r)
              (i := i - s.length) (show i - s.length < r.length by omega)
            rwa [show s.length + (i - s.length) = i from by omega] at h
          have h2 : (s ++ r)[i + 1]! = r[i - s.length + 1]! := by
            have h := aqs_getElemBang_append_right (s := s) (r := r)
              (i := i - s.length + 1) hi'
            rwa [show s.length + (i - s.length + 1) = i + 1 from by omega] at h
          rw [h1, h2]
          exact h

/-! ## §2 HOL AQ12.hl:1432 `contour_betwn_loop` -/

/-- **HOL `contour_betwn_loop`**（AQ12.hl:1432-:1463）：
`loop_list` 上的环段是 contour。HOL 走 `LAST_EL`/`card_set_of_list_uniq`/
`CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT` 三件（本树零命中）；Lean 直接用
`next_el_betwn_same`（在库 `aq10_nextElBetwnSame`）+ `next_el_EL`（本文件 §0）
把 flatten/parts 层全部绕开。 -/
theorem aqs_contourBetwnLoop {L : fgraph ℕ} {s : List (ℕ × ℕ)} {x y : ℕ × ℕ}
    (hnd : s.Nodup) (hloop : loopListSpine L s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : ContourListSpine L (between s x y) := by
  have hBnd : (between s x y).Nodup := uniqBetwn hnd hx hy hxy
  refine ⟨fun z hz => (hloop z (betwnMem hz)).1, ?_⟩
  intro i hi
  have hi0 : i < (between s x y).length := by omega
  have hd : (between s x y)[i] ∈ between s x y := List.getElem_mem hi0
  have hd_s : (between s x y)[i] ∈ s := betwnMem hd
  have hne : between s x y ≠ [] := List.ne_nil_of_mem hd
  -- d ≠ LAST（位置 i < len-1）
  have hdlast : (between s x y).getLast (List.ne_nil_of_mem hd) ≠ (between s x y)[i] := by
    intro hcon
    have hlast : (between s x y).getLast! = (between s x y)[(between s x y).length - 1]'
        (by have := List.length_pos_of_mem hd; omega) := aqs_getLastBang_last hne
    rw [← getLast!EqGetLast (List.ne_nil_of_mem hd)] at hcon
    rw [hlast] at hcon
    have := (List.Nodup.getElem_inj_iff hBnd).mp hcon
    omega
  -- next_el s d ∈ betwn（EQ_MEM_NEXT_EL_LAST）
  have hnext_mem : nextEl s ((between s x y)[i]) ∈ between s x y :=
    (aq10_eqMemNextElLast hxy hx hy hd hnd).mpr hdlast
  have hsame : nextEl (between s x y) ((between s x y)[i])
      = nextEl s ((between s x y)[i]) :=
    aq10_nextElBetwnSame hxy hx hy hd hnext_mem hnd
  have hstep := (hloop ((between s x y)[i]) hd_s).2
  rw [aqs_getElemBang hi0, aqs_getElemBang hi, ← aqs_nextElGetElem hBnd hi, hsame]
  exact hstep

/-! ## §3 HOL AQ12.hl:1464 `exists_conected_loop` -/

/-- **HOL `exists_conected_loop`**（AQ12.hl:1464-:1508）：
`uniq s ∧ loop_list L s ∧ x,y ∈ s ⇒ ∃ r, contour_list L r ∧ HD r = x ∧
LAST r = y ∧ set_of_list r ⊆ set_of_list s ∧ r ≠ []`。
构造 `r = [x] ++ betwn s x y ++ [y]`（HOL 同构造）；两处 junction 用
`HD_BETWN2`（本文件 `aqs_hdBetwn2`）与 `next_last_betwn`。 -/
theorem aqs_existsConnectedLoop {L : fgraph ℕ} {s : List (ℕ × ℕ)} {x y : ℕ × ℕ}
    (hs : s.Nodup) (hloop : loopListSpine L s) (hx : x ∈ s) (hy : y ∈ s) :
    ∃ r : List (ℕ × ℕ), ContourListSpine L r ∧ r.head! = x ∧ r.getLast! = y ∧
      setOfListSpine r ⊆ setOfListSpine s ∧ r ≠ [] := by
  have hxd : x ∈ listOfDarts L := (hloop x hx).1
  have hyd : y ∈ listOfDarts L := (hloop y hy).1
  have hxstep := (hloop x hx).2
  by_cases hxy : x = y
  · subst hxy
    refine ⟨[x], ((contourListCons L).2.1 x).mpr hxd, by simp, by simp, ?_, by simp⟩
    intro z hz
    change z ∈ [x] at hz
    rw [List.mem_singleton] at hz
    subst hz
    exact hx
  · have hcx : ContourListSpine L [x] := ((contourListCons L).2.1 x).mpr hxd
    have hcy : ContourListSpine L [y] := ((contourListCons L).2.1 y).mpr hyd
    -- (B ++ [y]) 的 contour
    have hcBy : ContourListSpine L (between s x y ++ [y]) := by
      by_cases hB : between s x y = []
      · rw [hB, List.nil_append]
        exact hcy
      · have hcat := (aqs_contourListCat (L := L) (s := between s x y) (r := [y])
          hB (by simp)).mpr
        refine hcat ⟨aqs_contourBetwnLoop hs hloop hx hy hxy, hcy, ?_⟩
        have hlast : (between s x y).getLast! = prevEl s y :=
          aqs_lastBetwnEqPrev hs hx hy hxy hB
        have hmemB : (between s x y).getLast! ∈ between s x y := aqs_getLastMem hB
        have hmemS : (between s x y).getLast! ∈ s := betwnMem hmemB
        have hstep := (hloop _ hmemS).2
        rw [hlast] at hstep ⊢
        rwa [nextElPrevElUniq hs y] at hstep
    -- junction：x → (B ++ [y]).head!
    have hjunc : oneStepListSpine L x (between s x y ++ [y]).head! := by
      by_cases hB : between s x y = []
      · rw [hB, List.nil_append, List.head!_cons]
        have hnext : nextEl s x = y := ((betwnNil hs hxy hx hy).mp hB).symm
        rwa [hnext] at hxstep
      · have hhead : (between s x y ++ [y]).head! = nextEl s x := by
          rw [aqs_headBang_append_eq hB, aqs_hdBetwn2 hs hx hy hxy hB]
        rw [hhead]
        exact hxstep
    refine ⟨[x] ++ (between s x y ++ [y]), ?_, ?_, ?_, ?_, by simp⟩
    · have hcat := (aqs_contourListCat (L := L) (s := [x]) (r := between s x y ++ [y])
        (by simp) (by simp)).mpr
      exact hcat ⟨hcx, hcBy, hjunc⟩
    · rw [aqs_headBang_append_eq (by simp : ([x] : List (ℕ × ℕ)) ≠ [])]
      rfl
    · rw [aqs_getLastAppend, if_neg (by simp : (between s x y ++ [y]) ≠ []),
        aqs_getLastAppend, if_neg (by simp : ([y] : List (ℕ × ℕ)) ≠ [])]
      rfl
    · intro z hz
      change z ∈ [x] ++ (between s x y ++ [y]) at hz
      rcases List.mem_append.mp hz with h | h
      · rw [List.mem_singleton] at h
        subst h
        exact hx
      · rcases List.mem_append.mp h with hB' | hy'
        · exact betwnMem hB'
        · rw [List.mem_singleton] at hy'
          subst hy'
          exact hy

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_nextEl_eq_getElem_succ
#print axioms Kepler.Text.TameSpine.aqs_nextElGetElem
#print axioms Kepler.Text.TameSpine.aqs_hdBetwn2
#print axioms Kepler.Text.TameSpine.aqs_contourListCat
#print axioms Kepler.Text.TameSpine.aqs_contourBetwnLoop
#print axioms Kepler.Text.TameSpine.aqs_existsConnectedLoop
