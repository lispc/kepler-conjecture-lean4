/-
  Kepler.Text.Reduction4K4C0R2d — K4-C0 R2d
  （reduction4.hl:4507 final_assumption_not_mem_snd_x_fy /
    :4600 final_assumption_not_mem_snd_x_zx）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction4K4C0R2b2
import Kepler.Text.Reduction4K4C0R2b1
import Kepler.Text.Reduction4K4C0
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5Ml1W5a
import Kepler.Text.Reduction5Ml1W4
import Kepler.Text.Reduction5Kbwpbhq
import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.Reduction4Subseg4
import Kepler.Text.Reduction4Subseg9
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.Reduction1W2e
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.TameList59

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4

open Kepler.Graphs (Face Graph fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl fList eList listOfDarts findFaceDarts listPairs)
open Kepler.Text.Reduction5
  (Dart core ntrans rtrans ytrans ztrans ftrans transformCount finalList ifbetwn indexf parts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList normalList)

/-! ## §0 桥件与小型辅助 -/

/-- 链世界 `indexf_add_betwn`（Spine 件经 `indexf_eq_spine` 桥）。 -/
private theorem indexfAddBetwnChain {s : List Dart} {x y z : Dart}
    (hne : x ≠ z) (hnd : s.Nodup) (hx : x ∈ s) (hy : y ∈ between s x z) (hz : z ∈ s) :
    indexf x y s + indexf y z s = indexf x z s := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine x y s,
    Kepler.Text.Reduction3.indexf_eq_spine y z s,
    Kepler.Text.Reduction3.indexf_eq_spine x z s]
  exact Kepler.Text.TameSpine.indexfAddBetwn hne hnd hx hy hz

/-- 链世界 `indexf_antisym`（Spine 件经桥）。 -/
private theorem indexfAntisymChain {s : List Dart} {x y : Dart}
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    indexf x y s + indexf y x s = s.length := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine x y s,
    Kepler.Text.Reduction3.indexf_eq_spine y x s]
  exact Kepler.Text.TameSpine.indexfAntisym hx hy hne

/-- 链世界 `indexf_lt_sizel`（Spine 件经桥）。 -/
private theorem indexfLtSizelChain {s : List Dart} {x y : Dart}
    (hx : x ∈ s) (hy : y ∈ s) : indexf x y s < s.length := by
  rw [Kepler.Text.Reduction3.indexf_eq_spine x y s]
  exact Kepler.Text.TameSpine.indexfLtSizel hx hy

/-- `ifbetwn` 不含其左端点（`not_betwn1` + 右端点互异）。 -/
private theorem notMemIfbetwnSelfLeft {α : Type} [DecidableEq α] {s : List α} {x z : α}
    (hnd : s.Nodup) (hx : x ∈ s) (hz : z ∈ s) (hxz : x ≠ z) :
    x ∉ ifbetwn s x z := by
  unfold Kepler.Text.Reduction5.ifbetwn
  by_cases hc : x ∈ s ∧ z ∈ s ∧ x ≠ z
  · rw [if_pos hc]
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact notBetwn1 hnd hz h
    · rcases List.mem_cons.mp h with h' | h'
      · exact hxz h'
      · exact absurd h' List.not_mem_nil
  · rw [if_neg hc]
    exact List.not_mem_nil

/-- 边非退化 ⇒ 端点互异（`edgeMap d = eList d = (SND d, FST d)`）。 -/
private theorem fstNeSndOfEdge (L : fgraph ℕ) (hL : GoodList L)
    (hen : (hypermapOfList L hL).EdgeNondegenerate) {d : Dart}
    (hd : d ∈ listOfDarts L) : d.1 ≠ d.2 := by
  have hmem : d ∈ (hypermapOfList L hL).darts := by
    have h' : d ∈ (↑(hypermapOfList L hL).darts : Set Dart) := by
      rw [Kepler.Text.TameLp.darts_hypermapOfList L hL]
      exact hd
    exact h'
  have hne := hen d hmem
  rw [Kepler.Text.TameLp.edgeMap_hypermapOfList L hL hmem] at hne
  intro h
  apply hne
  cases d with
  | mk a b =>
    simp only [Kepler.Assembly.eList, Prod.mk.injEq]
    exact ⟨h.symm, h⟩

/-! ## §R2d-1 `final_assumption_not_mem_snd_x_fy`（reduction4.hl:4507-4598） -/

/-- HOL `final_assumption_not_mem_snd_x_fy`（reduction4.hl:4507）：
`good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ ¬final ∧
transform_count = k ⇒ ∀ i < k，若 `ftrans i :: ifbetwn (core) (ftrans i) (FST y_i)`
长度 > 1，则 `SND x` 不在该 `ifbetwn` 中。
DIFFERS：Lean 惯例 +1 前提 `haq : AqiunppSlot`（供 `final_assumption_mem_uniq`）。 -/
theorem finalAssumptionNotMemSndXFy (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    ∀ i, i < k ∧ 1 < (ftrans L N r x i ::
        ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1).length →
      x.2 ∉ ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1 := by
  intro i ⟨hik, _⟩
  obtain ⟨hxD, hxf, hwf, hwr, hzrAll, hyrAll, hyfAll, hzfAll, hcoreN, hfnd, hk0⟩ :=
    Kepler.Text.Reduction5.finalAssumptionMemUniq L hL hgn hres haq k hm hnf hk
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hall : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hcore_nd : (core L r).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  set w : Dart := nextEl (findFaceDarts L x) x with hwdef
  have hw_r : w ∈ r := hwr
  have hw_f : w ∈ findFaceDarts L x := hwf
  have hnext_w : nextEl r x = w := hm.2.2.2.2.2.1
  have hwfst : w.1 = x.2 := Kepler.Text.Reduction5.fstNextFaceEqSnd L hL hgn hm hnf
  have hy_r : ytrans L N r x i ∈ r := hyrAll i hik
  have hy_f : ytrans L N r x i ∈ findFaceDarts L x := hyfAll i hik
  by_cases hft : ftrans L N r x i = (ytrans L N r x i).1
  · rw [hft, ifbetwnRefl]
    exact List.not_mem_nil
  by_cases hi0 : i = 0
  · -- `i = 0`：`ftrans 0 = SND x`，左端点即待证元素
    have hf0 : ftrans L N r x i = x.2 := by
      rw [Kepler.Text.Reduction5.ftrans, if_pos hi0]
    have hxb : x.2 ≠ (ytrans L N r x i).1 := by
      rw [← hf0]
      exact hft
    have hb_core : (ytrans L N r x i).1 ∈ core L r :=
      Kepler.Text.Reduction4Idx.memFstCore L hL hm hy_r
    have hxc_core : x.2 ∈ core L r := by
      have h := Kepler.Text.Reduction4Idx.memFstCore L hL hm hw_r
      rwa [hwfst] at h
    rw [hf0]
    exact notMemIfbetwnSelfLeft hcore_nd hxc_core hb_core hxb
  · -- `i > 0`：`ftrans i = FST (ztrans (i-1))`
    have hik1 : i - 1 < k := by omega
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
    have hftz : ftrans L N r x i = (ztrans L N r x (i - 1)).1 := by
      rw [Kepler.Text.Reduction5.ftrans, if_neg hi0]
    have hz_r : ztrans L N r x (i - 1) ∈ r := hzrAll (i - 1) hik1
    have hz_f : ztrans L N r x (i - 1) ∈ findFaceDarts L x := hzfAll (i - 1) hik1
    -- r 层 indexf 正性：`diowaasR` + `ryiuuvkR`
    have hf_im1 : ¬ finalList L (rtrans L N r x (i - 1)) :=
      Kepler.Text.Reduction4.transformCount_not (i - 1) (by rw [hk]; exact hik1)
    have hdiow := Kepler.Text.Reduction5.diowaasR L hL hgn hm (i - 1) hf_im1
      (w := w) hwdef.symm
    have hf_i : ¬ finalList L (rtrans L N r x ((i - 1) + 1)) := by
      rw [show i - 1 + 1 = i by omega]
      exact Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hik)
    have hry := Kepler.Text.Reduction5.ryiuuvkR L hL hgn hm (i - 1) hf_i
      (w := w) hwdef.symm
    rw [show i - 1 + 1 = i by omega] at hry
    have hzpos : 0 < indexf w (ztrans L N r x (i - 1)) r := by omega
    have hypos : 0 < indexf w (ytrans L N r x i) r := by omega
    have hwz : w ≠ ztrans L N r x (i - 1) := by
      intro h
      rw [h] at hzpos
      rw [Kepler.Text.Reduction4.indexfRefl hz_r] at hzpos
      omega
    have hwy : w ≠ ytrans L N r x i := by
      intro h
      rw [h] at hypos
      rw [Kepler.Text.Reduction4.indexfRefl hy_r] at hypos
      omega
    -- core_betwn 的 FST 互异前提
    have hbw : (ytrans L N r x i).1 ≠ w.1 := by
      intro h
      exact hwy (Kepler.Text.Reduction1.simpleList hxD hy_f hw_f h hall).symm
    have hwz_fst : w.1 ≠ (ztrans L N r x (i - 1)).1 := by
      intro h
      exact hwz (Kepler.Text.Reduction1.simpleList hxD hw_f hz_f h hall)
    have hbz : (ytrans L N r x i).1 ≠ (ztrans L N r x (i - 1)).1 := by
      intro h
      exact hft (hftz.trans h.symm)
    have hne_yz : ytrans L N r x i ≠ ztrans L N r x (i - 1) := by
      intro h
      apply hft
      rw [hftz, ← h]
    -- `w ∈ ifbetwn r y_i z`（cover + 反证）
    have hwyz : w ∈ ifbetwn r (ytrans L N r x i) (ztrans L N r x (i - 1)) := by
      refine (ifbetwnCover hrnd hy_r hz_r hw_r hne_yz).mpr ?_
      intro hmem2
      have hmem_bet : w ∈ @between Dart (instBEqOfDecidableEq : BEq Dart) r
          (ztrans L N r x (i - 1)) (ytrans L N r x i) := by
        unfold Kepler.Text.Reduction5.ifbetwn at hmem2
        by_cases hc : (ztrans L N r x (i - 1)) ∈ r ∧ (ytrans L N r x i) ∈ r ∧
            ztrans L N r x (i - 1) ≠ ytrans L N r x i
        · rw [if_pos hc] at hmem2
          rcases List.mem_append.mp hmem2 with h | h
          · exact h
          · rcases List.mem_cons.mp h with h' | h'
            · exact absurd h' hwy
            · exact absurd h' List.not_mem_nil
        · rw [if_neg hc] at hmem2
          exact absurd hmem2 List.not_mem_nil
      have hmem_betP : w ∈ @between Dart instBEqProd r
          (ztrans L N r x (i - 1)) (ytrans L N r x i) := by
        have heq : @between Dart (instBEqOfDecidableEq : BEq Dart) r
            (ztrans L N r x (i - 1)) (ytrans L N r x i)
            = @between Dart instBEqProd r
              (ztrans L N r x (i - 1)) (ytrans L N r x i) :=
          Kepler.Text.Reduction5.betweenEqOfLawful
            (e := (instBEqOfDecidableEq : BEq Dart)) (f := instBEqProd)
            (by infer_instance) (by infer_instance) r _ _
        exact heq ▸ hmem_bet
      have hadd : indexf (ztrans L N r x (i - 1)) w r +
          indexf w (ytrans L N r x i) r =
          indexf (ztrans L N r x (i - 1)) (ytrans L N r x i) r :=
        indexfAddBetwnChain (fun h => hne_yz h.symm) hrnd hz_r hmem_betP hy_r
      have hanti : indexf (ztrans L N r x (i - 1)) w r +
          indexf w (ztrans L N r x (i - 1)) r = r.length :=
        indexfAntisymChain hz_r hw_r (fun h => hwz h.symm)
      have hlt : indexf (ztrans L N r x (i - 1)) (ytrans L N r x i) r < r.length :=
        indexfLtSizelChain hz_r hy_r
      omega
    -- core_betwn 反向：`w.1 = SND x` 的 core 侧成员
    have hcb := coreBetwn L hL hgn hm hnf hm.1.edgeNondegenerate
      hy_r hw_r hz_r hbw hwz_fst hbz
    have hmem_core : x.2 ∈ ifbetwn (core L r) (ytrans L N r x i).1
        (ztrans L N r x (i - 1)).1 := by
      have h := hcb.mp hwyz
      rwa [hwfst] at h
    intro hmem
    rw [hftz] at hmem
    exact (ifbetwnDisjoint hcore_nd hmem) hmem_core

/-! ## §R2d-2 `final_assumption_not_mem_snd_x_zx`（reduction4.hl:4600-4673） -/

/-- HOL `final_assumption_not_mem_snd_x_zx`（reduction4.hl:4600）：
`good_list ∧ good_list_nodes ∧ is_restricted ∧ marked_list ∧ ¬final ∧
transform_count = k ⇒ SND x ∉ ifbetwn (core L r) (FST (ztrans (PRE k))) (FST x)`。
DIFFERS：Lean 惯例 +1 前提 `haq : AqiunppSlot`（供 `final_assumption_mem_uniq`）。 -/
theorem finalAssumptionNotMemSndXZx (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    x.2 ∉ ifbetwn (core L r) (ztrans L N r x (k - 1)).1 x.1 := by
  obtain ⟨hxD, hxf, hwf, hwr, hzrAll, hyrAll, hyfAll, hzfAll, hcoreN, hfnd, hk0⟩ :=
    Kepler.Text.Reduction5.finalAssumptionMemUniq L hL hgn hres haq k hm hnf hk
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hall : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hcore_nd : (core L r).Nodup :=
    Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm
  have hx_r : x ∈ r := hm.2.2.2.1
  have hkm1 : k - 1 < k := by omega
  have hz_r : ztrans L N r x (k - 1) ∈ r := hzrAll (k - 1) hkm1
  have hz_f : ztrans L N r x (k - 1) ∈ findFaceDarts L x := hzfAll (k - 1) hkm1
  set w : Dart := nextEl (findFaceDarts L x) x with hwdef
  have hw_r : w ∈ r := hwr
  have hw_f : w ∈ findFaceDarts L x := hwf
  have hnext_w : nextEl r x = w := hm.2.2.2.2.2.1
  have hwfst : w.1 = x.2 := Kepler.Text.Reduction5.fstNextFaceEqSnd L hL hgn hm hnf
  have hxs : x.1 ≠ x.2 := fstNeSndOfEdge L hL hm.1.edgeNondegenerate hxD
  by_cases hzx : (ztrans L N r x (k - 1)).1 = x.1
  · rw [hzx, ifbetwnRefl]
    exact List.not_mem_nil
  · -- `w ≠ z`（`diowaasR` 的正性）
    have hf_km1 : ¬ finalList L (rtrans L N r x (k - 1)) :=
      Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; exact hkm1)
    have hdiow := Kepler.Text.Reduction5.diowaasR L hL hgn hm (k - 1) hf_km1
      (w := w) hwdef.symm
    have hzpos : 0 < indexf w (ztrans L N r x (k - 1)) r := by omega
    have hwz : w ≠ ztrans L N r x (k - 1) := by
      intro h
      rw [h] at hzpos
      rw [Kepler.Text.Reduction4.indexfRefl hz_r] at hzpos
      omega
    -- `x ≠ w`（否则 `r = [x]` 且 `final_list L r`）
    have hxw : x ≠ w := by
      intro hxw
      have hnext : nextEl r x = x := hnext_w.trans hxw.symm
      have hnext' : @nextEl Dart (instBEqOfDecidableEq) r x = x :=
        (Kepler.Text.Reduction5.nextElInstEq r x) ▸ hnext
      have hr_eq : r = [x] :=
        Kepler.Text.MoreLemma2Island1.nextElRefl hx_r hnext' hrnd
      have hfin : finalList L r := by
        rw [hr_eq]
        intro d hd
        rw [List.mem_singleton] at hd
        subst d
        show fList L x = nextEl [x] x
        calc fList L x = w := rfl
          _ = x := hxw.symm
          _ = nextEl [x] x := by simp [Kepler.Assembly.nextEl]
      exact hnf hfin
    have hwne : w ≠ x := fun h => hxw h.symm
    have h1lt : 1 < r.length :=
      Kepler.Text.TameSpine.sizelGt1 hx_r hw_r hxw
    have hnext_w' : @nextEl Dart (instBEqOfDecidableEq) r x = w :=
      (Kepler.Text.Reduction5.nextElInstEq r x) ▸ hnext_w
    have hif1 : indexf x w r = 1 :=
      Kepler.Text.MoreLemma2Island1.nextElIndexf hx_r hw_r hrnd hnext_w' h1lt
    have hzx_ne : x.1 ≠ (ztrans L N r x (k - 1)).1 := fun h => hzx h.symm
    have hz_ne_x : ztrans L N r x (k - 1) ≠ x := by
      intro h
      exact hzx_ne (by rw [h])
    have hposz : 0 < indexf x (ztrans L N r x (k - 1)) r := by
      apply Nat.pos_of_ne_zero
      intro h0
      exact hzx_ne (congrArg Prod.fst (indexf_eq_zero hx_r hz_r h0))
    -- `w ∈ ifbetwn r x z`
    have hmem_r : w ∈ ifbetwn r x (ztrans L N r x (k - 1)) := by
      rw [ifbetwnIndexf hx_r hw_r hz_r hrnd]
      constructor
      · rw [hif1]; omega
      · rw [hif1]; omega
    -- core_betwn（u := x, v := w, w := z）
    have hxw_fst : x.1 ≠ w.1 := by
      rw [hwfst]
      exact hxs
    have hwz_fst : w.1 ≠ (ztrans L N r x (k - 1)).1 := by
      intro h
      exact hwz (Kepler.Text.Reduction1.simpleList hxD hw_f hz_f h hall)
    have hcb := coreBetwn L hL hgn hm hnf hm.1.edgeNondegenerate
      hx_r hw_r hz_r hxw_fst hwz_fst hzx_ne
    have hmem_core : x.2 ∈ ifbetwn (core L r) x.1 (ztrans L N r x (k - 1)).1 := by
      have h := hcb.mp hmem_r
      rwa [hwfst] at h
    intro hmem
    exact (ifbetwnDisjoint hcore_nd hmem) hmem_core

end Kepler.Text.Reduction4

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction4.finalAssumptionNotMemSndXFy
#print axioms Kepler.Text.Reduction4.finalAssumptionNotMemSndXZx
