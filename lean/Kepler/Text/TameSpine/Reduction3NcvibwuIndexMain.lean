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
import Kepler.Text.TameSpine.Reduction3BetwnIdxAux

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


/-- 槽 `hZlt` 填充（依赖 `hZidx`；w,z ∈ r' + `indexfLtSizel`）。 -/
private theorem fillHZlt (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w)
    (hZidx : indexf w (lZSpine L N r x) (rtransSpine L N r x 1)
      = indexf w (lZSpine L N r x) f) :
    indexf w (lZSpine L N r x) f < (rtransSpine L N r x 1).length := by
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hwr' : w ∈ rtransSpine L N r x 1 := by
    have hcase := aqs_nextMarkCaseMem L hL hgn (N := N) (r := r) (x := x) hm hf
      (f := f) (w := w) hfind hw
    rcases hcase with h | h
    · rw [h, rtransCat L N r x hf hrnd]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))
    · rw [rtransCat L N r x hf hrnd]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  have hzr' : lZSpine L N r x ∈ rtransSpine L N r x 1 := by
    rw [rtransCat L N r x hf hrnd]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))
  rw [← hZidx]
  exact indexfLtSizel hwr' hzr'


/-! ## §3 共用步引理（段 A：hBoff / hBlen 的换名与轨道桥） -/

/-- nextEl 幂保成员（B2b 私件同款重推导）。 -/
private theorem orbitMemFill {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    {a : α} (ha : a ∈ s) : ∀ k : ℕ, (nextEl s)^[k] a ∈ s := by
  intro k
  induction k with
  | zero => exact ha
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact Kepler.Text.TameLp.nextEl_mem_of_mem ih

/-- face 段移位：`(nextEl f)^[k] w = (nextEl f)^[k+1] x`（w = nextEl f x）。
换名三步（先 w→f x，再逆向合迭代——显式钉死内层 `nextEl f x`）。 -/
private theorem faceIterShift {f : List (ℕ × ℕ)} {x w : ℕ × ℕ} (hw : nextEl f x = w)
    (k : ℕ) : (nextEl f)^[k] w = (nextEl f)^[k + 1] x := by
  rw [← hw, ← Function.iterate_succ_apply]

/-- face 段入 r-弧（hnestFill 换名形）：`j < lM ⇒ (nextEl f)^[j] w ∈ B`。 -/
private theorem faceSegMemBetwn (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) (j : ℕ) (hj : j < lMSpine L r x) :
    (nextEl f)^[j] w ∈ between r (lZSpine L N r x) (lYSpine L r x) := by
  have h := hnestFill L hL hgn hm hf j hj
  rw [hfind] at h
  rw [← hw, ← Function.iterate_succ_apply]
  exact h

/-- face 段移位（函数侧合成形）：`(nextEl f)^[k+1] w = nextEl f ((nextEl f)^[k] w)`。 -/
private theorem faceIterStep {f : List (ℕ × ℕ)} {x w : ℕ × ℕ} (hw : nextEl f x = w)
    (k : ℕ) : (nextEl f)^[k + 1] w = nextEl f ((nextEl f)^[k] w) := by
  rw [← hw]
  exact Function.iterate_succ_apply' (nextEl f) k (nextEl f x)

/-- r/face 轨道一致性换名（`loopFaceAgree` 的步形）：
`j + 2 ≤ lM + 1 ⇒ nextEl r ((nextEl f)^[j] w) = nextEl f ((nextEl f)^[j] w)`。 -/
private theorem nextElRAgreeFace (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) (j : ℕ) (hj : j + 2 ≤ lMSpine L r x + 1) :
    nextEl r ((nextEl f)^[j] w) = nextEl f ((nextEl f)^[j] w) := by
  have hagree := loopFaceAgree L hL hgn hunL hm hf
  have hd0 : (nextEl f)^[j] w = (nextEl r)^[j + 1] x := by
    rw [← hw, ← Function.iterate_succ_apply, ← hfind, hagree (j + 1) (by omega)]
  have hd2 : (nextEl r)^[j + 2] x = (nextEl f)^[j + 2] x := by
    rw [hagree (j + 2) (by omega), ← hfind]
  have hd3 : (nextEl f)^[j + 2] x = (nextEl f)^[j + 1] w := by
    rw [← hw, ← Function.iterate_succ_apply]
  calc nextEl r ((nextEl f)^[j] w)
      = nextEl r ((nextEl r)^[j + 1] x) := by rw [hd0]
    _ = (nextEl r)^[j + 2] x := (Function.iterate_succ_apply' (nextEl r) (j + 1) x).symm
    _ = (nextEl f)^[j + 2] x := hd2
    _ = nextEl f ((nextEl f)^[j + 1] x) := Function.iterate_succ_apply' (nextEl f) (j + 1) x
    _ = nextEl f ((nextEl f)^[j] w) := by rw [faceIterShift hw j]

/-- B-内后继位（betwnOrbit 位移形）：界内 `nextEl s e = B[idxOf e + 1]`。 -/
private theorem betwnSuccOfLt {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {a b e : α} (hne : a ≠ b) (hnd : s.Nodup) (ha : a ∈ s) (hb : b ∈ s)
    (he : e ∈ between s a b)
    (hj1 : (between s a b).idxOf e + 1 < (between s a b).length) :
    nextEl s e = (between s a b)[(between s a b).idxOf e + 1]'(by omega) := by
  have hBe : (between s a b)[(between s a b).idxOf e] = e := getElem_idxOf he
  have h0 := (betwnOrbit (s := s) (a := a) (b := b) hne hnd ha hb
    (j := (between s a b).idxOf e + 1) hj1).symm
  have h1 := betwnOrbit (s := s) (a := a) (b := b) hne hnd ha hb
    (j := (between s a b).idxOf e)
    (by omega : (between s a b).idxOf e < (between s a b).length)
  have h2 : nextEl s ((between s a b)[(between s a b).idxOf e]'(by omega))
      = (nextEl s)^[(between s a b).idxOf e + 2] a := by
    rw [h1]
    exact (Function.iterate_succ_apply' (nextEl s)
      ((between s a b).idxOf e + 1) a).symm
  rw [← congrArg (nextEl s) hBe, h2, h0]

/-! ## §4 槽填充：`hBoff`（B-内偏移归纳） -/

/-- 槽 `hBoff` 填充：face 段 d_0..d_{lM-1} 的 r-弧内偏移恒等式
（位置归纳；步 = `nextElRAgreeFace` + `betwnLastIdx`，
he/hs 由 `faceSegMemBetwn` k、k+1 供）。 -/
private theorem fillHBoff (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) :
    ∀ i : ℕ, i < lMSpine L r x →
      (between r (lZSpine L N r x) (lYSpine L r x)).idxOf ((nextEl f)^[i] w)
        = (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + i := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hne : lZSpine L N r x ≠ lYSpine L r x :=
    Ne.symm (hqymrtx3List L hL hgn hunL hm hf)
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  intro i
  induction i with
  | zero => intro _; rfl
  | succ k ih =>
    intro hi
    have hk : k < lMSpine L r x := by omega
    have hmemk := faceSegMemBetwn L hL hgn hm hf hfind hw k hk
    have hmemk1 := faceSegMemBetwn L hL hgn hm hf hfind hw (k + 1) hi
    have hstep := nextElRAgreeFace L hL hgn hunL hm hf hfind hw k (by omega)
    have hgoalF : (nextEl f)^[k + 1] w = nextEl f ((nextEl f)^[k] w) :=
      faceIterStep hw k
    have hs : nextEl r ((nextEl f)^[k] w) ∈ between r (lZSpine L N r x) (lYSpine L r x) := by
      rw [hstep, ← hgoalF]; exact hmemk1
    have hlast := betwnLastIdx (s := r) (a := lZSpine L N r x) (b := lYSpine L r x)
      hne hrnd hzr hyr hmemk hs
    rw [hstep] at hlast
    rw [hgoalF, hlast, ih hk]
    omega

/-! ## §5 弧端点位置件（BetwnIdxAux `betwnPosEnd` 私件同证重推导） -/

/-- **弧端点位置**：`(idxOf a + 1 + |B|) % |s| = idxOf b`
（线性支 = idxOf b；wrap 支 = |s|+idxOf b 取模；sizeBetwn+indexfCond+omega）。 -/
private theorem betwnLenPos {α : Type} [BEq α] [LawfulBEq α] {s : List α} {a b : α}
    (hne : a ≠ b) (hnd : s.Nodup) (ha : a ∈ s) (hb : b ∈ s) :
    (s.idxOf a + 1 + (between s a b).length) % s.length = s.idxOf b := by
  have hsize := sizeBetwn hnd ha hb hne
  have hltb : s.idxOf b < s.length := List.idxOf_lt_length_iff.mpr hb
  have hidxa : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr ha
  rw [hsize, indexfCond ha hb]
  have hne2 : s.idxOf a ≠ s.idxOf b := fun heq =>
    hne ((List.idxOf_inj ha).mp heq)
  split
  · rename_i h1
    have hnum : s.idxOf a + 1 + (s.idxOf b - s.idxOf a - 1) = s.idxOf b := by omega
    rw [hnum, Nat.mod_eq_of_lt hltb]
  · rename_i h1
    have hnum : s.idxOf a + 1 + (s.idxOf b + (s.length - s.idxOf a) - 1)
        = s.length + s.idxOf b := by omega
    rw [hnum, Nat.add_comm (s.length) (s.idxOf b), Nat.add_mod_right,
      Nat.mod_eq_of_lt hltb]

/-! ## §6 槽填充：`hBlen`（末位定界） -/

/-- 槽 `hBlen` 填充：`|B| = B.idxOf w + lM`。
lM = 0 支：w = y（fillHYw）+ y∉B ⇒ B.idxOf y = |B|；
lM > 0 支：d_{lM-1} 的 r-后继 = y ∉ B ⇒ d_{lM-1} 居 B 末位
（反证：若 B.idxOf d + 1 < |B|，`betwnSuccOfLt` 给后继 ∈ B，撞 notBetwn2）。 -/
private theorem fillHBlen (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w)
    (hBoff : ∀ i : ℕ, i < lMSpine L r x →
      (between r (lZSpine L N r x) (lYSpine L r x)).idxOf ((nextEl f)^[i] w)
        = (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + i) :
    (between r (lZSpine L N r x) (lYSpine L r x)).length
      = (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + lMSpine L r x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hne : lZSpine L N r x ≠ lYSpine L r x :=
    Ne.symm (hqymrtx3List L hL hgn hunL hm hf)
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  set B := between r (lZSpine L N r x) (lYSpine L r x) with hBdef
  rcases Nat.eq_zero_or_pos (lMSpine L r x) with h0 | hpos
  · -- lM = 0：w = y
    have hwY := fillHYw L hL hgn hm hf hfind hw
    rw [h0] at hwY
    simp only [Function.iterate_zero, id_eq] at hwY
    have hnyB : lYSpine L r x ∉ B := notBetwn2 hrnd
    have hidxY : B.idxOf (lYSpine L r x) = B.length := List.idxOf_eq_length hnyB
    rw [hwY, hidxY, h0]
    omega
  · -- lM > 0：d_{lM-1} 末位定界
    have hkM : lMSpine L r x - 1 < lMSpine L r x := by omega
    have hdmem := faceSegMemBetwn L hL hgn hm hf hfind hw (lMSpine L r x - 1) hkM
    have hoff := hBoff (lMSpine L r x - 1) hkM
    have hstep := nextElRAgreeFace L hL hgn hunL hm hf hfind hw (lMSpine L r x - 1)
      (by omega)
    have hdY := fillHYw L hL hgn hm hf hfind hw
    have hM1 : lMSpine L r x - 1 + 1 = lMSpine L r x := by omega
    have hdY' : (nextEl f)^[lMSpine L r x - 1 + 1] w = lYSpine L r x := by
      rw [hM1]; exact hdY
    have hnextY : nextEl r ((nextEl f)^[lMSpine L r x - 1] w) = lYSpine L r x := by
      rw [hstep, ← faceIterStep hw (lMSpine L r x - 1), ← hdY']
    have hnyB : lYSpine L r x ∉ B := notBetwn2 hrnd
    have hilt : B.idxOf ((nextEl f)^[lMSpine L r x - 1] w) < B.length :=
      List.idxOf_lt_length_iff.mpr hdmem
    by_cases hcase : B.idxOf ((nextEl f)^[lMSpine L r x - 1] w) + 1 < B.length
    · exfalso
      have hsIn := betwnSuccOfLt (s := r) (a := lZSpine L N r x) (b := lYSpine L r x)
        hne hrnd hzr hyr hdmem hcase
      have hyin : lYSpine L r x ∈ B := by
        rw [← hnextY, hsIn]
        exact List.getElem_mem hcase
      exact hnyB hyin
    · have hlen : B.length = B.idxOf ((nextEl f)^[lMSpine L r x - 1] w) + 1 := by omega
      omega

/-! ## §7 槽填充：`hposW` -/

/-- 槽 `hposW` 填充：`r'.idxOf w = 1 + B.idxOf w`。
lM = 0 支：w = y（fillHYw），hposY 同款段位 + y∉B ⇒ B.idxOf y = |B|；
lM > 0 支：w ∈ B（faceSegMemBetwn 0），hposB 同款段位（idxOf_append_seg）。 -/
private theorem fillHWpos (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) :
    (rtransSpine L N r x 1).idxOf w
      = 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w := by
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
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
  set B := between r (lZSpine L N r x) (lYSpine L r x) with hBdef
  rcases Nat.eq_zero_or_pos (lMSpine L r x) with h0 | hpos
  · -- lM = 0：w = y
    have hwY := fillHYw L hL hgn hm hf hfind hw
    rw [h0] at hwY
    simp only [Function.iterate_zero, id_eq] at hwY
    -- hposY 同款：r'.idxOf y = |B| + 1
    have hposY : (rtransSpine L N r x 1).idxOf (lYSpine L r x) = B.length + 1 := by
      have h := idxOf_append_seg (P := [lZSpine L N r x] ++ B)
        (B := [lYSpine L r x])
        (S := between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x))
        (by rw [← hr'eq]; exact hnd') (i := 0) (by simp)
      have h0' : ([lYSpine L r x] : List (ℕ × ℕ))[0]'(by simp) = lYSpine L r x := rfl
      rw [h0'] at h
      rw [← hr'eq] at h
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] at h
      omega
    have hnyB : lYSpine L r x ∉ B := notBetwn2 hrnd
    have hidxY : B.idxOf (lYSpine L r x) = B.length := List.idxOf_eq_length hnyB
    rw [hwY, hposY, hidxY]
    omega
  · -- lM > 0：w ∈ B，hposB 同款段位
    have hwB : w ∈ B := faceSegMemBetwn L hL hgn hm hf hfind hw 0 hpos
    have heq : rtransSpine L N r x 1
        = [lZSpine L N r x] ++ B ++ ([lYSpine L r x] ++ between (findFaceDarts L
            (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)) := by
      rw [hr'eq, List.append_assoc]
    rw [heq]
    exact (congrArg (fun e => ([lZSpine L N r x]
        ++ B ++ ([lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (lZSpine L N r x))).idxOf e)
        (getElem_idxOf hwB)).symm.trans
      (idxOf_append_seg (P := [lZSpine L N r x])
        (B := B)
        (S := [lYSpine L r x] ++ between (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (lZSpine L N r x))
        (by rw [← heq]; exact hnd')
        (List.idxOf_lt_length_iff.mpr hwB))

/-! ## §8 槽填充：`hCmem` / `hCoff`（C 段：face-y 弧） -/

/-- 槽 `hCmem` 填充：`lM < i < idxZ ⇒ (nextEl f)^[i] w ∈ C`
（C = between (findFaceDarts L y) y z）。
证 = indexf 账：`indexf w d f = i`（nextElnIndexf）、`indexf w y f = lM`
（indexfYtransEqLm）、`indexfAddLeft` w→y→d 与 w→y→z ⇒
`0 < indexf y d f ∧ indexf y d f < indexf y z f`，`indexfBetwnEq` 收口
（face 换名 `findFaceDarts L y = findFaceDarts L x`，findFaceDarts_congr_of_mem）。 -/
private theorem fillHCmem (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) :
    ∀ i : ℕ, lMSpine L r x < i → i < indexf w (lZSpine L N r x) f →
      (nextEl f)^[i] w
        ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  obtain ⟨hyf, hzf⟩ := markedLemmaYzInFace L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxd : x ∈ Kepler.Assembly.listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  have hxx' : x ∈ f := by rw [← hfind]; exact hxx
  have hcongr : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    Kepler.Text.TameLp.findFaceDarts_congr_of_mem hL.1 hxd hyf
  have hndF : (findFaceDarts L (lYSpine L r x)).Nodup := by
    rw [hcongr]; exact findFaceDarts_nodup hL.1 x
  have hyF : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) := by
    rw [hcongr]; exact hyf
  have hzF : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) := by
    rw [hcongr]; exact hzf
  have hfnd : f.Nodup := by rw [← hfind]; exact findFaceDarts_nodup hL.1 x
  have hyf' : lYSpine L r x ∈ f := by rw [← hfind]; exact hyf
  have hzf' : lZSpine L N r x ∈ f := by rw [← hfind]; exact hzf
  have hwf : w ∈ f := by rw [← hw]; exact Kepler.Text.TameLp.nextEl_mem_of_mem hxx'
  have hMLm : indexf w (lYSpine L r x) f = lMSpine L r x := by
    have h := indexfYtransEqLm L hL hgn hunL hm hf
    rwa [hfind, hw] at h
  intro i hi hiz
  have hddf : (nextEl f)^[i] w ∈ f := orbitMemFill hwf i
  have hzlt : indexf w (lZSpine L N r x) f < f.length := indexfLtSizel hwf hzf'
  have hidxf : indexf w ((nextEl f)^[i] w) f = i :=
    nextElnIndexf hwf hddf hfnd rfl (by omega)
  have h1 := indexfAddLeft (s := f) hwf hyf' hddf (by rw [hMLm, hidxf]; omega)
  have h2 := indexfAddLeft (s := f) hwf hyf' hzf' (by rw [hMLm]; omega)
  rw [hMLm, hidxf] at h1
  rw [hMLm] at h2
  rw [indexfBetwnEq hyne hndF hyF hzF, hcongr, hfind]
  exact ⟨by omega, by omega⟩

/-- 槽 `hCoff` 填充（依赖 `hCmem`）：`lM < i < idxZ ⇒ C.idxOf ((nextEl f)^[i] w)
= i - lM - 1`。基例 i = lM+1：d_{lM+1} = nextEl f y = C[0]（betwnOrbit 0 位）；
步：d_{k+1} = nextEl f_y d_k（face 换名 hfy），
`betwnLastIdx`（s := findFaceDarts L y）给差 1。 -/
private theorem fillHCoff (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w)
    (hCmem : ∀ i : ℕ, lMSpine L r x < i → i < indexf w (lZSpine L N r x) f →
      (nextEl f)^[i] w
        ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)) :
    ∀ i : ℕ, lMSpine L r x < i → i < indexf w (lZSpine L N r x) f →
      (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).idxOf
        ((nextEl f)^[i] w)
        = i - lMSpine L r x - 1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  obtain ⟨hyf, hzf⟩ := markedLemmaYzInFace L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxd : x ∈ Kepler.Assembly.listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hcongr : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    Kepler.Text.TameLp.findFaceDarts_congr_of_mem hL.1 hxd hyf
  have hndF : (findFaceDarts L (lYSpine L r x)).Nodup := by
    rw [hcongr]; exact findFaceDarts_nodup hL.1 x
  have hyF : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) := by
    rw [hcongr]; exact hyf
  have hzF : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) := by
    rw [hcongr]; exact hzf
  have hCnd : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
      (lZSpine L N r x)).Nodup := uniqBetwn hndF hyF hzF hyne
  have hfy : findFaceDarts L (lYSpine L r x) = f := by rw [hcongr, hfind]
  have hdY := fillHYw L hL hgn hm hf hfind hw
  intro i
  induction i with
  | zero => intro hi _; exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro hi hiz
    have hmemk1 := hCmem (k + 1) hi hiz
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq | hlt
    · -- 基例 k = lM：d_{lM+1} = nextEl f y = C[0]
      have hCpos : 0 < (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).length := List.length_pos_of_mem hmemk1
      have hC0' : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x))[0]'hCpos = nextEl f (lYSpine L r x) := by
        have hC0 := betwnOrbit (s := findFaceDarts L (lYSpine L r x))
          (a := lYSpine L r x) (b := lZSpine L N r x) hyne hndF hyF hzF (j := 0) hCpos
        rw [hC0, Function.iterate_succ_apply, Function.iterate_zero_apply, hfy]
      have hd1 : (nextEl f)^[k + 1] w
          = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
              (lZSpine L N r x))[0]'hCpos := by
        rw [hC0', ← heq, faceIterStep hw (lMSpine L r x), hdY]
      rw [hd1, hCnd.idxOf_getElem 0 hCpos]
      omega
    · -- 步：k > lM，IH 于 k
      have hik := ih hlt (by omega)
      have hmemk := hCmem k hlt (by omega)
      have hstepF : nextEl (findFaceDarts L (lYSpine L r x)) ((nextEl f)^[k] w)
          = (nextEl f)^[k + 1] w := by
        rw [hfy, faceIterStep hw k]
      have hs : nextEl (findFaceDarts L (lYSpine L r x)) ((nextEl f)^[k] w)
          ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x) := by
        rw [hstepF]; exact hmemk1
      have hlast := betwnLastIdx (s := findFaceDarts L (lYSpine L r x))
        (a := lYSpine L r x) (b := lZSpine L N r x) hyne hndF hyF hzF hmemk hs
      rw [hstepF] at hlast
      rw [hlast, hik]
      omega

/-! ## §9 槽填充：`hZidx`（z 的 indexf 账） -/

/-- 槽 `hZidx` 填充（依赖 `hposW` / `hBlen`）：`indexf w l'z r' = indexf w l'z f`。
r' 侧：`r'.idxOf l'z = 0`（hposZ 同款）、`r'.idxOf w = 1 + bw`（hposW）、
`|r'| = |B| + |C| + 2`、`|B| = bw + lM`（hBlen）⇒ `indexf w l'z r' = lM + |C| + 1`；
f 侧：`indexfAddLeft` w→y→z（lM + indexf y z f = idxZ）+ `sizeBetwn`
（|C| = indexf y z f_y − 1）⇒ `idxZ = lM + |C| + 1`。 -/
private theorem fillHZidx (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w)
    (hposW : (rtransSpine L N r x 1).idxOf w
      = 1 + (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w)
    (hBlen : (between r (lZSpine L N r x) (lYSpine L r x)).length
      = (between r (lZSpine L N r x) (lYSpine L r x)).idxOf w + lMSpine L r x) :
    indexf w (lZSpine L N r x) (rtransSpine L N r x 1)
      = indexf w (lZSpine L N r x) f := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
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
  obtain ⟨hyf, hzf⟩ := markedLemmaYzInFace L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxd : x ∈ Kepler.Assembly.listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (Kepler.Text.TameLp.dart_in_face L x).mpr hxd
  have hxx' : x ∈ f := by rw [← hfind]; exact hxx
  have hcongr : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
    Kepler.Text.TameLp.findFaceDarts_congr_of_mem hL.1 hxd hyf
  have hndF : (findFaceDarts L (lYSpine L r x)).Nodup := by
    rw [hcongr]; exact findFaceDarts_nodup hL.1 x
  have hyF : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) := by
    rw [hcongr]; exact hyf
  have hzF : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) := by
    rw [hcongr]; exact hzf
  have hyf' : lYSpine L r x ∈ f := by rw [← hfind]; exact hyf
  have hzf' : lZSpine L N r x ∈ f := by rw [← hfind]; exact hzf
  have hwf : w ∈ f := by rw [← hw]; exact Kepler.Text.TameLp.nextEl_mem_of_mem hxx'
  have hMLm : indexf w (lYSpine L r x) f = lMSpine L r x := by
    have h := indexfYtransEqLm L hL hgn hunL hm hf
    rwa [hfind, hw] at h
  have hMLtz : lMSpine L r x < indexf w (lZSpine L N r x) f := by
    have h := (pplhuljV0 L hL hgn hunL hm hf).2.2
    rw [hfind, hw] at h
    rw [hMLm] at h
    exact h
  -- f 侧：idxZ = lM + |C| + 1
  have hIdx : indexf w (lZSpine L N r x) f
      = lMSpine L r x + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).length + 1 := by
    have h2 := indexfAddLeft (s := f) hwf hyf' hzf' (by rw [hMLm]; omega)
    rw [hMLm] at h2
    have hC := sizeBetwn (s := findFaceDarts L (lYSpine L r x)) hndF hyF hzF hyne
    have hCy : indexf (lYSpine L r x) (lZSpine L N r x)
        (findFaceDarts L (lYSpine L r x))
        = indexf (lYSpine L r x) (lZSpine L N r x) f := by rw [hcongr, hfind]
    rw [hCy] at hC
    omega
  -- r' 侧成员性与位置账
  have hlen' : (rtransSpine L N r x 1).length
      = (between r (lZSpine L N r x) (lYSpine L r x)).length
        + (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x)).length + 2 := by
    rw [hr'eq]
    simp only [List.length_append, List.length_cons, List.length_nil]
    ring
  have hwlt : (rtransSpine L N r x 1).idxOf w < (rtransSpine L N r x 1).length := by
    rw [hposW, hlen']
    omega
  have hwmem : w ∈ rtransSpine L N r x 1 := List.idxOf_lt_length_iff.mp hwlt
  have hzmem : lZSpine L N r x ∈ rtransSpine L N r x 1 := by
    rw [hr'eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))
  have hposZ : (rtransSpine L N r x 1).idxOf (lZSpine L N r x) = 0 := by
    have hlt : 0 < (rtransSpine L N r x 1).length := List.length_pos_of_mem hzmem
    have h0 : (rtransSpine L N r x 1)[0]! = lZSpine L N r x := by
      rw [hr'eq]
      simp
    have hstep := hnd'.idxOf_getElem 0 hlt
    have heq : (rtransSpine L N r x 1)[0]'hlt = lZSpine L N r x := by
      rw [← getElemBangH hlt]
      exact h0
    rwa [heq] at hstep
  rw [indexf, if_pos ⟨hwmem, hzmem⟩, hposZ, hposW, hlen', hBlen, hIdx,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## §10 NCVIBWU i=0 组合装配（槽全闭） -/

/-- **NCVIBWU i=0（spine 载体，槽全闭）**：`j ≤ indexf w l'z f ⇒
face 轨道第 j 步 ∈ r' ∧ `indexf w d r' = j`。
成员半 = B2e `ohcgkfuSpineV0`；index 半 = 槽版 `ncvibwuV0IdxSpine` + 九槽填充
（fillHWpos / fillHBoff / fillHBlen / fillHCoff / fillHCmem / fillHYw / fillHZw /
fillHZidx / fillHZlt）。 -/
theorem ncvibwuV0FullSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {j : ℕ}
    (hj : j ≤ indexf w (lZSpine L N r x) f) :
    (nextEl f)^[j] w ∈ rtransSpine L N r x 1 ∧
      indexf w ((nextEl f)^[j] w) (rtransSpine L N r x 1) = j := by
  have hBoff := fillHBoff L hL hgn hm hf hfind hw
  have hBlen := fillHBlen L hL hgn hm hf hfind hw hBoff
  have hposW := fillHWpos L hL hgn hm hf hfind hw
  have hCmem := fillHCmem L hL hgn hm hf hfind hw
  have hCoff := fillHCoff L hL hgn hm hf hfind hw hCmem
  have hZidx := fillHZidx L hL hgn hm hf hfind hw hposW hBlen
  exact ⟨ohcgkfuSpineV0 L hL hgn hm hf hfind hw hj,
    ncvibwuV0IdxSpine L hL hgn hm hf hfind hw hposW hBoff hBlen hCoff hCmem
      (fillHYw L hL hgn hm hf hfind hw) (fillHZw L hL hgn hm hf hfind hw)
      hZidx (fillHZlt L hL hgn hm hf hfind hw hZidx) hj⟩

/-- **NCVIBWU i=0（chain 载体，槽全闭）**：成员半 = `ncvibwuV0MemChain`
（chain 直投）；index 半 = `ncvibwuV0FullSpine` 经 `lzEqSpine` / `rtransEqSpine`
桥翻译回 chain 载体。 -/
theorem ncvibwuV0FullChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hs : Kepler.Text.ChainLists.sList L r x = sListSpine L r x)
    (hf : ¬ Kepler.Text.Reduction5.finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {j : ℕ}
    (hj : j ≤ indexf w (Kepler.Text.Reduction5.lz L N r x) f) :
    (nextEl f)^[j] w ∈ Kepler.Text.Reduction5.rtrans L N r x 1 ∧
      indexf w ((nextEl f)^[j] w) (Kepler.Text.Reduction5.rtrans L N r x 1) = j := by
  refine ⟨ncvibwuV0MemChain L hL hgn hunL haq hm hs hf hfind hw hj, ?_⟩
  have hmS : MarkedListSpineFull hL N r x :=
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm
  have hfS : ¬ finalListSpine L r := hf
  have hlz : Kepler.Text.Reduction5.lz L N r x = lZSpine L N r x :=
    Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hf
  have hbridge : Kepler.Text.Reduction5.rtrans L N r x 1 = rtransSpine L N r x 1 :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm 1
  rw [hlz] at hj
  rw [hbridge]
  exact (ncvibwuV0FullSpine L hL hgn hmS hfS hfind hw hj).2

end Kepler.Text.TameSpine

-- 公理审计锚（编译即执行；预期标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.ncvibwuV0IdxSpine

-- 槽填充探针
#print axioms Kepler.Text.TameSpine.fillHZlt
#print axioms Kepler.Text.TameSpine.fillHZw
#print axioms Kepler.Text.TameSpine.fillHYw

-- §3/§4 探针（段 A 首件）
#print axioms Kepler.Text.TameSpine.fillHBoff
#print axioms Kepler.Text.TameSpine.betwnLenPos
#print axioms Kepler.Text.TameSpine.fillHBlen
#print axioms Kepler.Text.TameSpine.fillHWpos
#print axioms Kepler.Text.TameSpine.fillHCmem
#print axioms Kepler.Text.TameSpine.fillHCoff
#print axioms Kepler.Text.TameSpine.fillHZidx
#print axioms Kepler.Text.TameSpine.ncvibwuV0FullSpine
#print axioms Kepler.Text.TameSpine.ncvibwuV0FullChain
