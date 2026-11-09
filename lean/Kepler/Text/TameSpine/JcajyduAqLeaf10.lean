/-
  JcajyduAqLeaf10 — AQ10 叶 helper/gap 批（AQ10-a 5 件 + AQ10-a2 8 件）。
  HOL 锚：betwnEqNil AQ4:41 · memFindFaceImpFacesEq lhm:424 · fListPowerNextEl
  PWSSRAT:502 · nextElBetwnSame NCVIBWU:131 · eqMemNextElLast AQ4:60 ·
  memNextElIterate/nextElPeriod（MEM_POWER_NEXT_EL/周回）· nextMarkMemRTrans
  AQ1:586 · lYRepPowerLe NCVIBWU:190 · memNextMarkInface PPLHULJ:97 ·
  indexfYtransEqLm1 AQ7:39 · indexfConstLe AQ7:128 · indexfYLeZInR0 AQ7:181。
  未做：aq10_pointRemarkMemSplit（AQ10:39-95，留 AQ10-a3）；主证 aq10（AQ10-b）。
  载体：Dart=ℕ×ℕ；between（Graphs）、findFaceDarts/nextEl/fList（Assembly）、
  lYSpine/lZSpine；债根已清（TameList16:1109 真证）。
-/

import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList53
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.TameSpine.JcajyduAqZIndexf
import Kepler.Text.TameSpine.JcajyduAqTowerBase
import Kepler.Text.MoreLemma2a23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl fList findFaceDarts listOfDarts GoodList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-! ## §1 `Aq4.betwn_eq_nil`（betwnNil 直取） -/

/-- HOL `Aq4.betwn_eq_nil`（AQ4.hl:41）：`betwn r y z = [] ∧ MEM y r ∧
MEM z r ∧ ~(y = z) ∧ uniq r ⇒ next_el r y = z`。 -/
theorem aq10_betwnEqNil {α : Type} [BEq α] [LawfulBEq α] {r : List α} {y z : α}
    (hb : Kepler.Graphs.between r y z = []) (hy : y ∈ r) (hz : z ∈ r)
    (hne : y ≠ z) (hnd : r.Nodup) :
    nextEl r y = z :=
  ((betwnNil hnd hne hy hz).mp hb).symm

/-! ## §2 `List_hypermap.mem_find_face_imp_faces_eq` -/

/-- HOL `mem_find_face_imp_faces_eq`（list_hypermap-compiled.hl:424）：
`uniq (list_of_darts L) ∧ MEM d1 (find_face L d2) ⇒
find_face L d1 = find_face L d2`。 -/
theorem aq10_memFindFaceImpFacesEq {L : fgraph ℕ} (hn : (listOfDarts L).Nodup)
    {d1 d2 : ℕ × ℕ} (hd : d1 ∈ findFaceDarts L d2) :
    findFaceDarts L d1 = findFaceDarts L d2 := by
  by_cases hval : L.find? (fun l => decide (d2 ∈ Kepler.Assembly.listPairs l)) = none
  · rw [Kepler.Text.TameLp.findFaceDarts_none hval] at hd
    exact absurd hd (by simp)
  · obtain ⟨l', hs⟩ := Option.ne_none_iff_exists.mp hval
    obtain ⟨hfeq, -, hl'⟩ := Kepler.Text.TameLp.findFaceDarts_some hs.symm
    rw [hfeq] at hd ⊢
    exact Kepler.Text.TameLp.findFaceDarts_eq_of_mem hn hl' hd

/-! ## §3 `Pwssrat.f_list_power_next_el` -/

/-- HOL `f_list_power_next_el`（PWSSRAT.hl:502）：`uniq (list_of_darts L) ∧
MEM y (list_of_darts L) ⇒ (f_list L)^m y = (next_el (find_face L y))^m y`。
（`fList L d = nextEl (findFaceDarts L d) d` 定义级；轨道不离开 `find_face`。） -/
theorem aq10_fListPowerNextEl {L : fgraph ℕ} (hn : (listOfDarts L).Nodup)
    {y : ℕ × ℕ} (hy : y ∈ listOfDarts L) (m : ℕ) :
    (fList L)^[m] y = ((nextEl (findFaceDarts L y))^[m]) y := by
  have hface : y ∈ findFaceDarts L y := by
    rw [listOfDarts, List.mem_flatten] at hy
    obtain ⟨l, hl, hyl⟩ := hy
    obtain ⟨l₀, hl₀, hll⟩ := List.mem_map.mp hl
    have hyl' : y ∈ Kepler.Assembly.listPairs l₀ := by rw [hll]; exact hyl
    rw [Kepler.Text.TameLp.findFaceDarts_eq_of_mem hn hl₀ hyl']
    exact hyl'
  have hiter : ∀ k : ℕ, ((nextEl (findFaceDarts L y))^[k]) y ∈ findFaceDarts L y := by
    intro k
    induction k with
    | zero => simpa using hface
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Kepler.Text.TameLp.nextEl_mem_of_mem ih
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    have hd := hiter m
    have hff : findFaceDarts L (((nextEl (findFaceDarts L y))^[m]) y)
        = findFaceDarts L y := aq10_memFindFaceImpFacesEq hn hd
    simp only [fList, hff]

/-- `getElem` 在 `idxOf` 处的取值（同表不同界证的 proof irrelevance 直给）。 -/
private theorem aq10_getElemIdxOf {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hx : x ∈ s) {j : ℕ} (hj : j = s.idxOf x) (hj' : j < s.length) :
    s[j]'hj' = x := by
  subst hj
  exact Kepler.Text.TameLp.getElem_idxOf hx

/-! ## §4 `Ncvibwu.next_el_betwn_same` -/

/-- HOL `next_el_betwn_same`（NCVIBWU.hl:131）：`~(y=z) ∧ MEM y f ∧ MEM z f ∧
MEM d (betwn f y z) ∧ MEM (next_el f d) (betwn f y z) ∧ uniq f ⇒
next_el (betwn f y z) d = next_el f d`。证明走 indexl_betwn 双侧 + indexf
加一（`indexfN`/`nextElnIndexf`）+ getElem 定位。 -/
theorem aq10_nextElBetwnSame {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {f : List α} {y z d : α} (hyz : y ≠ z) (hy : y ∈ f) (hz : z ∈ f)
    (hd : d ∈ between f y z) (hnext : nextEl f d ∈ between f y z) (hnd : f.Nodup) :
    nextEl (between f y z) d = nextEl f d := by
  have hndB := uniqBetwn hnd hy hz hyz
  have hdf : d ∈ f := betwnMem hd
  have hnf : nextEl f d ∈ f := betwnMem hnext
  have h1 : (between f y z).idxOf d + 1 = indexf y d f := indexlBetwn hnd hy hz hd
  have h2 : (between f y z).idxOf (nextEl f d) + 1 = indexf y (nextEl f d) f :=
    indexlBetwn hnd hy hz hnext
  have hdbetw := indexfBetwn (x := y) (y := d) (z := z) hyz hnd hy hz hd
  have hzlt : indexf y z f < f.length := indexfLtSizel hy hz
  have hlt : indexf y d f + 1 < f.length := by omega
  have hiter : (nextEl f)^[indexf y d f] y = d := indexfN hy hdf hnd
  have hstep : (nextEl f)^[indexf y d f + 1] y = nextEl f d := by
    rw [Function.iterate_succ_apply', hiter]
  have hidxN : indexf y (nextEl f d) f = indexf y d f + 1 :=
    nextElnIndexf hy hnf hnd hstep hlt
  have hidxB : (between f y z).idxOf (nextEl f d) = (between f y z).idxOf d + 1 := by
    omega
  have hlt2 : (between f y z).idxOf d + 1 < (between f y z).length := by
    rw [← hidxB]
    exact List.idxOf_lt_length_iff.mpr hnext
  have hnextElEq : nextEl (between f y z) d
      = (between f y z).getD ((between f y z).idxOf d + 1) d := by
    unfold Kepler.Assembly.nextEl
    rw [if_neg (by omega : ¬((between f y z).idxOf d = (between f y z).length - 1))]
  rw [hnextElEq, Kepler.Text.TameLp.getD_eq_getElem_of_lt hlt2 d]
  exact aq10_getElemIdxOf hnext (by omega) hlt2

/-! ## §5 `Aq4.EQ_MEM_NEXT_EL_LAST` -/

/-- HOL `EQ_MEM_NEXT_EL_LAST`（AQ4.hl:60）：`~(y=z) ∧ MEM y f ∧ MEM z f ∧
MEM d (betwn f y z) ∧ uniq f ⇒
(MEM (next_el f d) (betwn f y z) ↔ LAST (betwn f y z) ≠ d)`。 -/
theorem aq10_eqMemNextElLast {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {f : List α} {y z d : α} (hyz : y ≠ z) (hy : y ∈ f) (hz : z ∈ f)
    (hd : d ∈ between f y z) (hnd : f.Nodup) :
    (nextEl f d ∈ between f y z) ↔
      (between f y z).getLast (List.ne_nil_of_mem hd) ≠ d := by
  have hBne : between f y z ≠ [] := List.ne_nil_of_mem hd
  constructor
  · intro hnext hlast
    have hnl := nextLastBetwn (r := f) (y := y) (z := z) hy hz hnd hyz hBne
    rw [hlast] at hnl
    exact notBetwn2 hnd (hnl ▸ hnext)
  · intro hlastne
    have hdf : d ∈ f := betwnMem hd
    have hnf : nextEl f d ∈ f := Kepler.Text.TameLp.nextEl_mem_of_mem hdf
    have hdbetw := indexfBetwn (x := y) (y := d) (z := z) hyz hnd hy hz hd
    have hzlt : indexf y z f < f.length := indexfLtSizel hy hz
    have hlt : indexf y d f + 1 < f.length := by omega
    have hiter : (nextEl f)^[indexf y d f] y = d := indexfN hy hdf hnd
    have hstep : (nextEl f)^[indexf y d f + 1] y = nextEl f d := by
      rw [Function.iterate_succ_apply', hiter]
    have hidxN : indexf y (nextEl f d) f = indexf y d f + 1 :=
      nextElnIndexf hy hnf hnd hstep hlt
    rw [indexfBetwnEq hyz hnd hy hz]
    constructor
    · omega
    · by_contra hge
      have heq : indexf y (nextEl f d) f = indexf y z f := by omega
      have hnz : nextEl f d = z := by
        have h1 : (nextEl f)^[indexf y (nextEl f d) f] y = nextEl f d := indexfN hy hnf hnd
        have h2 : (nextEl f)^[indexf y z f] y = z := indexfN hy hz hnd
        rw [heq] at h1
        exact h1.symm.trans h2
      have hidxB : (between f y z).idxOf d + 1 = indexf y d f :=
        indexlBetwn hnd hy hz hd
      have hsize := sizeBetwn hnd hy hz hyz
      have hlen : (between f y z).idxOf d = (between f y z).length - 1 := by omega
      have hdlast : (between f y z).getLast hBne = d := by
        rw [List.getLast_eq_getElem hBne]
        exact aq10_getElemIdxOf (s := between f y z) (x := d) hd (by omega) (by omega)
      exact hlastne hdlast

/-! ## §6 nextEl 周回 / 迭代成员（`MEM_POWER_NEXT_EL` 形） -/

/-- `next_el` 迭代不出表（HOL `MEM_POWER_NEXT_EL` / `memNextElIterate` 形）。 -/
theorem aq10_memNextElIterate {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hx : x ∈ s) : ∀ k : ℕ, (nextEl s)^[k] x ∈ s := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact Kepler.Text.TameLp.nextEl_mem_of_mem ih

/-- `(a % n + 1) % n = (a + 1) % n`。 -/
private theorem aq10_modSuccMod (a n : ℕ) : (a % n + 1) % n = (a + 1) % n := by
  have h : a + 1 = n * (a / n) + (a % n + 1) := by
    have := Nat.div_add_mod a n
    omega
  rw [h, Nat.add_comm (n * (a / n)), Nat.add_mul_mod_self_left]

/-- idxOf 沿 nextEl 迭代的模长平移。 -/
private theorem aq10_idxOfNextElIterate {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {x : α} (hnd : s.Nodup) (hx : x ∈ s) :
    ∀ k : ℕ, s.idxOf ((nextEl s)^[k] x) = (s.idxOf x + k) % s.length := by
  intro k
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.add_zero,
      Nat.mod_eq_of_lt (List.idxOf_lt_length_iff.mpr hx)]
  | succ k ih =>
    rw [Function.iterate_succ_apply', idxOfNextElMod hnd (aq10_memNextElIterate hx k), ih,
      ← Nat.add_assoc, aq10_modSuccMod]

/-- 周回：`(nextEl s)^[s.length] y = y`（nodup + 成员）。 -/
theorem aq10_nextElPeriod {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {y : α} (hnd : s.Nodup) (hy : y ∈ s) :
    (nextEl s)^[s.length] y = y := by
  have hiylt : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hidx : s.idxOf ((nextEl s)^[s.length] y) = s.idxOf y := by
    rw [aq10_idxOfNextElIterate hnd hy]
    have h : s.idxOf y + s.length = s.length + s.idxOf y := Nat.add_comm _ _
    rw [h, Nat.add_mod_left, Nat.mod_eq_of_lt hiylt]
  have hmem := aq10_memNextElIterate hy s.length
  have hilt : s.idxOf ((nextEl s)^[s.length] y) < s.length :=
    List.idxOf_lt_length_iff.mpr hmem
  have hmid : s[s.idxOf ((nextEl s)^[s.length] y)]'hilt
      = s[s.idxOf y]'hiylt := by
    have h := congrArg (fun i => s.getD i y) hidx
    rwa [Kepler.Text.TameLp.getD_eq_getElem_of_lt hilt,
      Kepler.Text.TameLp.getD_eq_getElem_of_lt hiylt] at h
  calc (nextEl s)^[s.length] y
      = s[s.idxOf ((nextEl s)^[s.length] y)]'hilt :=
        (List.getElem_idxOf hilt).symm
    _ = s[s.idxOf y]'hiylt := hmid
    _ = y := List.getElem_idxOf hiylt

/-! ## §7 AQ7 上游四件 + `indexf_ytrans_eq_l_m1_v0` -/

/-- HOL `Aq1.next_mark_mem_r_trans_v0`（AQ1.hl:586）：
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧
find_face L x = f ∧ next_el f x = w ⇒ MEM w r`。 -/
theorem aq10_nextMarkMemRTrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) :
    nextEl (findFaceDarts L x) x ∈ r := by
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hxr : x ∈ r := hm.1.2.2.2.1
  show fList L x ∈ r
  rw [← hnext]
  exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr

/-- HOL `Ncvibwu.l_y_rep_power_le`（NCVIBWU.hl:190）：
`f_list L x = next_el r x ⇒ ∀ j ≤ l'm, (f_list L)^(j+1) x = (next_el r)^(j+1) x`。 -/
theorem aq10_lYRepPowerLe (L : fgraph ℕ) (r : List (ℕ × ℕ)) (x : ℕ × ℕ)
    (hnext : fList L x = nextEl r x) :
    ∀ j : ℕ, j ≤ lMSpine L r x → (fList L)^[j + 1] x = (nextEl r)^[j + 1] x := by
  intro j hj
  have h := minNotEqImpEq (nextEl r) (fList L) x (lMSpine L r x) rfl j hj
  rw [← hnext] at h
  calc (fList L)^[j + 1] x = (fList L)^[j] (fList L x) :=
        Function.iterate_succ_apply (fList L) j x
    _ = (nextEl r)^[j + 1] x := h.symm

/-- HOL `Pplhulj.mem_next_mark_inface`（PPLHULJ.hl:97）：
`good_list L ∧ marked_list L N r x ∧ f = find_face L x ∧ w = next_el f x ⇒
MEM w (find_face L x)`。 -/
theorem aq10_memNextMarkInface (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) :
    nextEl (findFaceDarts L x) x ∈ findFaceDarts L x := by
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hxr := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hrN, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  exact Kepler.Text.TameLp.nextEl_mem_of_mem hxx

/-- HOL `Aq7.indexf_ytrans_eq_l_m1_v0`（AQ7.hl:39）：`~(final_list L r) ∧
good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧ next_el r x = w ⇒
indexf w (ytrans L N r x 0) r = l'm L r x`。 -/
theorem aq10_indexfYtransEqLm1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r = lMSpine L r x := by
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hw : nextEl (findFaceDarts L x) x ∈ r := aq10_nextMarkMemRTrans L hL hgn hm
  have hnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hwEq : nextEl (findFaceDarts L x) x = nextEl r x := hnext.symm
  have hyW : lYSpine L r x = (nextEl r)^[lMSpine L r x] (nextEl (findFaceDarts L x) x) := by
    rw [lYRepPower L r x hnext.symm]
    rw [Function.iterate_succ_apply, ← hwEq]
  have hlt : lMSpine L r x < r.length := by
    have hlen : 0 < r.length := List.length_pos_of_mem hxr
    by_cases hne : ({m : ℕ | (nextEl r)^[m + 2] x
        ≠ fList L ((nextEl r)^[m + 1] x)} : Set ℕ).Nonempty
    · by_contra hge
      push Not at hge
      have hmem : lMSpine L r x
          ∈ {m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)} :=
        Nat.sInf_mem hne
      have hstep : lMSpine L r x - r.length
          ∈ {m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)} := by
        have e1 : (nextEl r)^[lMSpine L r x + 2] x
            = (nextEl r)^[(lMSpine L r x - r.length) + 2] x := by
          rw [show lMSpine L r x + 2 = ((lMSpine L r x - r.length) + 2) + r.length from by omega,
            Function.iterate_add_apply, aq10_nextElPeriod hnd hxr]
        have e2 : (nextEl r)^[lMSpine L r x + 1] x
            = (nextEl r)^[(lMSpine L r x - r.length) + 1] x := by
          rw [show lMSpine L r x + 1 = ((lMSpine L r x - r.length) + 1) + r.length from by omega,
            Function.iterate_add_apply, aq10_nextElPeriod hnd hxr]
        simp only [Set.mem_setOf_eq] at hmem ⊢
        rw [← e1, ← e2]
        exact hmem
      have hle : lMSpine L r x ≤ lMSpine L r x - r.length := Nat.sInf_le hstep
      omega
    · have h0 : lMSpine L r x = 0 := by
        unfold Kepler.Text.TameSpine.lMSpine Kepler.Text.TameSpine.minNumSpine
        rw [Set.not_nonempty_iff_eq_empty.mp hne, Nat.sInf_empty]
      omega
  exact nextElnIndexf hw hy hnd hyW.symm hlt

/-! ## §8 `Aq7.indexf_const_le_indexf_ytrans_v0` + `indexf_y_le_z_in_r_0` -/

/-- `l'm < sizel (find_face L x)`（ZIndexf `indexfYtransEqLm` 内的界，同证重落）。 -/
private theorem aq10_lmLtFaceLen (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lMSpine L r x < (findFaceDarts L x).length := by
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hxr := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hrN, hxr⟩)
  have hsc := markListSplitConditionList L hL hm.1 hf
  have hsplit := splitConditionListSplit L hL hgn (by
    have := hm.1.1
    exact fun l hl => by
      have hun := isRestrictedAllUniq L hL hgn this
      exact hun l hl) hsc
  have hM := hypMLm L hL hgn (by
    have := hm.1.1
    exact fun l hl => by
      have hun := isRestrictedAllUniq L hL hgn this
      exact hun l hl) hnext hsc
  have hlt := (Kepler.Text.TameLp.hypermapOfList L hL).hypM_lt_face hsplit
  rw [hM] at hlt
  have hcard := cardFaceOfList L hL hxd
  rw [hcard] at hlt
  omega

/-- HOL `Aq7.indexf_const_le_indexf_ytrans_v0`（AQ7.hl:128）：
`marked_list ∧ ~final_list ∧ MEM d r ∧
indexf w d r ≤ indexf w y_0 r ⇒ indexf w d r = indexf w d (find_face L x)`，
其中 `w = next_el (find_face L x) x`。 -/
theorem aq10_indexfConstLe (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {d : ℕ × ℕ} (hd : d ∈ r)
    (hle : indexf (nextEl (findFaceDarts L x) x) d r
      ≤ indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r) :
    indexf (nextEl (findFaceDarts L x) x) d r
      = indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x) := by
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hn := hm.1.2.1
  have hrN := hm.1.2.2.1
  have hnd : r.Nodup := (normalListUniqNonnil hn hrN).1
  have hw : nextEl (findFaceDarts L x) x ∈ r := aq10_nextMarkMemRTrans L hL hgn hm
  have hY : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r = lMSpine L r x :=
    aq10_indexfYtransEqLm1 L hL hgn hm hf
  have hle' : indexf (nextEl (findFaceDarts L x) x) d r ≤ lMSpine L r x := by
    rw [← hY]; exact hle
  have hiterR : (nextEl r)^[indexf (nextEl (findFaceDarts L x) x) d r]
      (nextEl (findFaceDarts L x) x) = d := indexfN hw hd hnd
  have hwEq : nextEl (findFaceDarts L x) x = nextEl r x := hnext.symm
  have hstepR : (nextEl r)^[indexf (nextEl (findFaceDarts L x) x) d r + 1] x = d := by
    rw [Function.iterate_succ_apply, ← hwEq]
    exact hiterR
  have hLY := aq10_lYRepPowerLe L r x hnext.symm
    (indexf (nextEl (findFaceDarts L x) x) d r) hle'
  have hfl : (fList L)^[indexf (nextEl (findFaceDarts L x) x) d r + 1] x = d :=
    hLY.trans hstepR
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hn x (List.mem_flatten.mpr ⟨r, hrN, hxr⟩)
  have hface : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  have hfpow := aq10_fListPowerNextEl (L := L) (by
      rw [listOfDarts]; exact hL.1) (y := x) hxd
      (indexf (nextEl (findFaceDarts L x) x) d r + 1)
  -- (nextEl f)^[idx] w = d
  have hflW : (nextEl (findFaceDarts L x))^[indexf (nextEl (findFaceDarts L x) x) d r]
      (nextEl (findFaceDarts L x) x) = d := by
    rw [show (nextEl (findFaceDarts L x))^[indexf (nextEl (findFaceDarts L x) x) d r]
          (nextEl (findFaceDarts L x) x)
        = (nextEl (findFaceDarts L x))^[indexf (nextEl (findFaceDarts L x) x) d r + 1] x from by
      rw [Function.iterate_succ_apply]]
    rw [← hfpow]
    exact hfl
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x :=
    aq10_memNextMarkInface L hL hgn hm
  have hdf : d ∈ findFaceDarts L x := hflW ▸ aq10_memNextElIterate hwf _
  have hlt : indexf (nextEl (findFaceDarts L x) x) d r
      < (findFaceDarts L x).length := by
    have := aq10_lmLtFaceLen L hL hgn hm hf
    omega
  have hF : indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x)
      = indexf (nextEl (findFaceDarts L x) x) d r :=
    nextElnIndexf hwf hdf (Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x) hflW hlt
  exact hF.symm

/-- HOL `Aq7.indexf_y_le_z_in_r_0`（AQ7.hl:181）：`marked_list ∧ ~final_list ⇒
indexf w y_0 r < indexf w z_0 r`（`w = next_el (find_face L x) x`）。 -/
theorem aq10_indexfYLeZInR0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r
      < indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) r := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hconstY := aq10_indexfConstLe L hL hgn hm hf hy (Nat.le_refl _)
  have hconstZ := aq10_indexfConstLe L hL hgn hm hf hz
  by_contra hge
  push Not at hge
  have hle : indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) r
      ≤ indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r := by omega
  have hZ := hconstZ hle
  have hY := hconstY
  have hlt := hpp.2.2
  rw [← hZ, ← hY] at hlt
  omega

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq10_betwnEqNil
#print axioms Kepler.Text.TameSpine.aq10_memFindFaceImpFacesEq
#print axioms Kepler.Text.TameSpine.aq10_fListPowerNextEl
#print axioms Kepler.Text.TameSpine.aq10_nextElBetwnSame
#print axioms Kepler.Text.TameSpine.aq10_eqMemNextElLast
#print axioms Kepler.Text.TameSpine.aq10_memNextElIterate
#print axioms Kepler.Text.TameSpine.aq10_nextElPeriod
#print axioms Kepler.Text.TameSpine.aq10_nextMarkMemRTrans
#print axioms Kepler.Text.TameSpine.aq10_lYRepPowerLe
#print axioms Kepler.Text.TameSpine.aq10_memNextMarkInface
#print axioms Kepler.Text.TameSpine.aq10_indexfYtransEqLm1
#print axioms Kepler.Text.TameSpine.aq10_indexfConstLe
#print axioms Kepler.Text.TameSpine.aq10_indexfYLeZInR0
