/-
  Kepler.Text.TameSpine.Reduction3NcvibwuIndexMain — NCVIBWU i=0 index 半（槽版）。
  真证：r' 位置账（hposB/hposY/hposC/hposZ）+ hcore 模算术 + j<lM / j=lM / lM<j<idxZ 三支。
  显式槽（下波填，共 9 条）：hposW（r'.idxOf w = 1+B.idxOf w）/hBoff（B-内偏移）/
  hBlen（|B|=bw+lM）/hCoff（C-内偏移）/hCmem（C 成员性）/hYw（lM 位=y）/
  hZw（idxZ 位=z）/hZidx（z 的 indexf 账）/hZlt（idxZ < r'.length）。

  纪律：零禁词；主仓双零写入。
-/
import Kepler.Text.TameSpine.Reduction3NcvibwuGateFirst
import Kepler.Text.TameSpine.Reduction3NcvibwuIndexFirst
import Kepler.Text.TameSpine.JcajyduRed2Trans

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList prevEl)
open Kepler.Text.TameLp (GoodListNodesTl getElem_idxOf findFaceDarts_nodup)
open Kepler.Text.Reduction5 (Dart)

/-- 界内 `getElem!` 与依赖式 `getElem` 同值。 -/
private theorem getElemBangH {α : Type} [Inhabited α] {l : List α} {i : Nat}
    (h : i < l.length) : l[i]! = l[i]'h := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

/-- **NCVIBWU i=0 index 半（槽版）**：`j ≤ indexf w l'z f ⇒
indexf w ((nextEl f)^[j] w) (rtransSpine 1) = j`。 -/
theorem ncvibwuV0IdxSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w)
    (hposW : (rtransSpine L N r x 1).idxOf w
      = 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w)
    (hBoff : ∀ i : ℕ, i < lMSpine L r x →
      (between r (lZSpine L N r x) (lYSpine L r x)).idxOf ((nextEl f)^[i] w)
        = (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + i)
    (hBlen : (between r (lZSpine L N r x) (lYSpine L r x)).length
        = (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + lMSpine L r x)
    (hCoff : ∀ i : ℕ, lMSpine L r x < i → i < indexf w (lZSpine L N r x) f →
      (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).idxOf
        ((nextEl f)^[i] w)
        = i - lMSpine L r x - 1)
    (hCmem : ∀ i : ℕ, lMSpine L r x < i → i < indexf w (lZSpine L N r x) f →
      (nextEl f)^[i] w
        ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))
    (hYw : (nextEl f)^[lMSpine L r x] w = lYSpine L r x)
    (hZw : (nextEl f)^[indexf w (lZSpine L N r x) f] w = lZSpine L N r x)
    (hZidx : indexf w (lZSpine L N r x) (rtransSpine L N r x 1)
      = indexf w (lZSpine L N r x) f)
    (hZlt : indexf w (lZSpine L N r x) f < (rtransSpine L N r x 1).length)
    {j : ℕ} (hj : j ≤ indexf w (lZSpine L N r x) f) :
    indexf w ((nextEl f)^[j] w) (rtransSpine L N r x 1) = j := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  obtain ⟨hyf, hzf⟩ := markedLemmaYzInFace L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hndNt : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hr'eq : rtransSpine L N r x 1
      = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x])
        ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) :=
    rtransCat L N r x hf hrnd
  have hnd' : (rtransSpine L N r x 1).Nodup := by
    have h1 : rtransSpine L N r x 1
        = (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
      show ((transformListSpine L x)^[1] (N, r)).2 = _
      rw [Function.iterate_one]
      simp only [transformListSpine, if_neg hf]
    have hmemS : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 ∈ ntransSpine L N r x 1 :=
      sndMemRtran1 L hm.1.2.2.1 hf
    rw [h1]
    exact uniqFlattenUniq _ hndNt _ hmemS
  -- 位置账（真证）
  have hposB : ∀ d ∈ between r (lZSpine L N r x) (lYSpine L r x),
      (rtransSpine L N r x 1).idxOf d
        = 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf d := by
    intro d hd
    have heq : rtransSpine L N r x 1
        = [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
              (lYSpine L r x) (lZSpine L N r x)) := by
      rw [hr'eq, List.append_assoc]
    rw [heq]
    exact (congrArg (fun e => ([lZSpine L N r x]
        ++ between r (lZSpine L N r x) (lYSpine L r x)
        ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (lZSpine L N r x))).idxOf e)
        (getElem_idxOf hd)).symm.trans
      (idxOf_append_seg (P := [lZSpine L N r x])
        (B := between r (lZSpine L N r x) (lYSpine L r x))
        (S := [lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (lZSpine L N r x))
        (by rw [← heq]; exact hnd')
        (List.idxOf_lt_length_iff.mpr hd))
  have hposY : (rtransSpine L N r x 1).idxOf (lYSpine L r x)
      = (between r (lZSpine L N r x) (lYSpine L r x)).length + 1 := by
    have h := idxOf_append_seg (P := [lZSpine L N r x]
        ++ between r (lZSpine L N r x) (lYSpine L r x))
        (B := [lYSpine L r x])
        (S := between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))
        (by rw [← hr'eq]; exact hnd') (i := 0) (by simp)
    have h0 : ([lYSpine L r x] : List (ℕ × ℕ))[0]'(by simp) = lYSpine L r x := rfl
    rw [h0] at h
    rw [← hr'eq] at h
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] at h
    omega
  have hposC : ∀ d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x),
      (rtransSpine L N r x 1).idxOf d
        = (between r (lZSpine L N r x) (lYSpine L r x)).length + 2
          + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).idxOf d := by
    intro d hd
    have hnd2 : ((([lZSpine L N r x]
        ++ between r (lZSpine L N r x) (lYSpine L r x)) ++ [lYSpine L r x])
        ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).Nodup := by
      rw [← hr'eq]; exact hnd'
    have hdisj : d ∉ ([lZSpine L N r x]
        ++ between r (lZSpine L N r x) (lYSpine L r x)) ++ [lYSpine L r x] := by
      intro hdP
      exact ((List.nodup_append.mp hnd2).2.2 _ hdP _ hd) rfl
    have h := List.idxOf_append_of_notMem
      (l₂ := between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x)) hdisj
    rw [← hr'eq] at h
    rw [h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hposZ : (rtransSpine L N r x 1).idxOf (lZSpine L N r x) = 0 := by
    have hzmem : lZSpine L N r x ∈ rtransSpine L N r x 1 := by
      rw [hr'eq]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))
    have hlt : 0 < (rtransSpine L N r x 1).length := List.length_pos_of_mem hzmem
    have h0 : (rtransSpine L N r x 1)[0]! = lZSpine L N r x := by
      rw [hr'eq]
      simp
    have hstep := hnd'.idxOf_getElem 0 hlt
    have heq : (rtransSpine L N r x 1)[0]'hlt = lZSpine L N r x := by
      rw [← getElemBangH hlt]
      exact h0
    rwa [heq] at hstep
  have hposW' : (rtransSpine L N r x 1).idxOf w
      = 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w := hposW
  -- 主算术：r'.idxOf d = 1 + bw + j ⇒ indexf = j
  have hcore : ∀ d : ℕ × ℕ, d ∈ rtransSpine L N r x 1 →
      (rtransSpine L N r x 1).idxOf d
        = 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + j →
      indexf w d (rtransSpine L N r x 1) = j := by
    intro d hdm hq
    have hlen : (rtransSpine L N r x 1).length
        = (between r (lZSpine L N r x) (lYSpine L r x)).length
          + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).length + 2 := by
      rw [hr'eq]
      simp only [List.length_append, List.length_cons, List.length_nil]
      ring
    have hwlt : (rtransSpine L N r x 1).idxOf w < (rtransSpine L N r x 1).length := by
      rw [hposW', hlen]
      omega
    have hwmem : w ∈ rtransSpine L N r x 1 := List.idxOf_lt_length_iff.mp hwlt
    rw [indexf, if_pos ⟨hwmem, hdm⟩]
    rw [hq, hposW', hlen]
    have hsum : (1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + j)
        + ((between r (lZSpine L N r x) (lYSpine L r x)).length
          + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).length + 2
          - (1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w))
        = j + ((between r (lZSpine L N r x) (lYSpine L r x)).length
          + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x)).length + 2) := by
      have hle : 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w
          ≤ (between r (lZSpine L N r x) (lYSpine L r x)).length
            + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                (lZSpine L N r x)).length + 2 := by
        have := hBlen
        omega
      have hsub : ((between r (lZSpine L N r x) (lYSpine L r x)).length
            + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                (lZSpine L N r x)).length + 2
            - (1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w))
          + (1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w)
          = (between r (lZSpine L N r x) (lYSpine L r x)).length
            + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                (lZSpine L N r x)).length + 2 :=
        Nat.sub_add_cancel hle
      have hsc : (1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w)
          + ((between r (lZSpine L N r x) (lYSpine L r x)).length
            + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                (lZSpine L N r x)).length + 2
            - (1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w))
          = (between r (lZSpine L N r x) (lYSpine L r x)).length
            + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
                (lZSpine L N r x)).length + 2 :=
        Nat.add_sub_cancel' hle
      omega
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- 分支
  rcases Nat.lt_or_ge j (lMSpine L r x) with hlt | hge
  · -- j < lM：d ∈ B
    have hdmem : (nextEl f)^[j] w ∈ between r (lZSpine L N r x) (lYSpine L r x) := by
      have h := hnestFill L hL hgn hm hf j hlt
      rw [hfind, Function.iterate_succ_apply, hw] at h
      exact h
    have hq : (rtransSpine L N r x 1).idxOf ((nextEl f)^[j] w)
        = 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + j := by
      rw [hposB _ hdmem, hBoff j hlt]
      omega
    have hdm : (nextEl f)^[j] w ∈ rtransSpine L N r x 1 := by
      rw [hr'eq]
      exact List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ hdmem))
    exact hcore _ hdm hq
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · -- j = lM：d = y
      have hq : (rtransSpine L N r x 1).idxOf ((nextEl f)^[j] w)
          = 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + j := by
        rw [← heq, hYw, hposY, hBlen]
        omega
      have hdm : (nextEl f)^[j] w ∈ rtransSpine L N r x 1 := by
        rw [← heq, hYw]
        rw [hr'eq]
        exact List.mem_append_left _
          (List.mem_append_right _ (List.mem_cons_self ..))
      exact hcore _ hdm hq
    · rcases Nat.lt_or_eq_of_le hj with hltZ | heqZ
      · -- lM < j < idxZ：d ∈ C
        have hdmem : (nextEl f)^[j] w ∈ between (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (lZSpine L N r x) := hCmem j hgt hltZ
        have hq : (rtransSpine L N r x 1).idxOf ((nextEl f)^[j] w)
            = 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + j := by
          rw [hposC _ hdmem, hCoff j hgt hltZ, hBlen]
          omega
        have hdm : (nextEl f)^[j] w ∈ rtransSpine L N r x 1 := by
          rw [hr'eq]
          exact List.mem_append_right _ hdmem
        exact hcore _ hdm hq
      · -- j = idxZ：d = z（槽 hZw + hZidx）
        have hd : (nextEl f)^[j] w = lZSpine L N r x := by
          rw [heqZ]
          exact hZw
        rw [hd, hZidx]
        exact heqZ.symm


/-! ## §2 槽填充：`hZw` / `hYw`（本轮两条；其余 7 槽修法表见 DELIVERY） -/

/-- 槽 `hZw` 填充：`(nextEl f)^[indexf w z f] w = z`（`indexfN` on f + 换名）。 -/
private theorem fillHZw (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) :
    (nextEl f)^[indexf w (lZSpine L N r x) f] w = lZSpine L N r x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  obtain ⟨hyf, hzf⟩ := markedLemmaYzInFace L hL hgn hunL hm hf
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxd : x ∈ Kepler.Assembly.listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  have hxx' : x ∈ f := by rw [← hfind]; exact hxx
  have hfnd' : f.Nodup := by rw [← hfind]; exact findFaceDarts_nodup hL.1 x
  have hzf' : lZSpine L N r x ∈ f := by rw [← hfind]; exact hzf
  have hw' : w ∈ f := by rw [← hw]; exact Kepler.Text.TameLp.nextEl_mem_of_mem hxx'
  exact indexfN hw' hzf' hfnd'

/-- 槽 `hYw` 填充：`(nextEl f)^[lM] w = y`（`dLMeqY` + `indexfYtransEqLm`）。 -/
private theorem fillHYw (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) :
    (nextEl f)^[lMSpine L r x] w = lYSpine L r x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hMLm : indexf w (lYSpine L r x) f = lMSpine L r x := by
    have h := indexfYtransEqLm L hL hgn hunL hm hf
    rwa [hfind, hw] at h
  have h2 : (nextEl f)^[indexf w (lYSpine L r x) f] w = lYSpine L r x := by
    have h := dLMeqY L hL hgn hunL hm hf
    rwa [hfind, hw] at h
  rw [hMLm] at h2
  exact h2

end Kepler.Text.TameSpine

-- 公理审计锚（编译即执行；预期标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.ncvibwuV0IdxSpine

-- 槽填充探针
#print axioms Kepler.Text.TameSpine.fillHZw
#print axioms Kepler.Text.TameSpine.fillHYw
