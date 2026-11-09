/-
  Kepler.Text.TameSpine.JcajyduAqLeaf10 — AQ10-a 批（helper + gap，7 件）。

  ┌─ 件目 ────────────────────────────────────────────────────────
  │ aq10_betwnEqNil              Aq4.betwn_eq_nil (AQ4.hl:41)
  │ aq10_memFindFaceImpFacesEq   List_hypermap.mem_find_face_imp_faces_eq
  │ aq10_fListPowerNextEl        Pwssrat.f_list_power_next_el (PWSSRAT.hl:502)
  │ aq10_nextElBetwnSame         Ncvibwu.next_el_betwn_same (NCVIBWU.hl:131)
  │ aq10_eqMemNextElLast         Aq4.EQ_MEM_NEXT_EL_LAST (AQ4.hl:60)
  │ aq10_indexfConstLe           Aq7.indexf_const_le_indexf_ytrans_v0 (AQ7.hl:128)
  │ aq10_indexfYLeZInR0          Aq7.indexf_y_le_z_in_r_0 (AQ7.hl:181)
  │ aq10_pointRemarkMemSplit     AQ10.hl:39-95
  │ 主证 aq10 不在本批（AQ10-b）。indexfConstLe/indexfYLeZInR0/
  │ pointRemarkMemSplit 三件经审计需另 5 个上游（见 DELIVERY L10-4），
  │ 本批未做、留 AQ10-a2。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体 / DIFFERS ────────────────────────────────────────────
  │ 链/Spine 共同量：`Dart = ℕ × ℕ`；`findFaceDarts`（Assembly）、
  │ `nextEl`/`prevEl`（Assembly）、`between`（Graphs）、`fList`（Assembly）。
  │ l'y/l'z ↦ `lYSpine`/`lZSpine`；z/y 成员性由 `zMemRtransClean`/
  │ `ytransMemRtrans`（干净、标准三）供给，不触 TameList16:1109 债。
  └────────────────────────────────────────────────────────────────
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

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq10_betwnEqNil
#print axioms Kepler.Text.TameSpine.aq10_memFindFaceImpFacesEq
#print axioms Kepler.Text.TameSpine.aq10_fListPowerNextEl
#print axioms Kepler.Text.TameSpine.aq10_nextElBetwnSame
#print axioms Kepler.Text.TameSpine.aq10_eqMemNextElLast
