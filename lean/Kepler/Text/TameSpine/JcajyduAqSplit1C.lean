/-
  Kepler.Text.TameSpine.JcajyduAqSplit1C — E4c：`aq3Concl` split.1 支的两条**排除件**
  （HOL AQ1.hl:612 `next_r_not_eq_f_v0` / AQ1.hl:690 `prev_r_not_eq_f_v0`）。

  件目（2 件，全真证）：
  ① `nextRNotEqF`：`nextEl r (l'y) ≠ fList L (l'y)`（marked_list + ¬final）；
  ② `prevRNotEqF`：`fList L (prevEl r (l'z)) ≠ l'z`（同上 + GoodListNodes）。

  **路线（比 HOL 短得多，零新几何件）**：
  - ① `nextRNotEqF`：HOL 走 `next_mark_mem_r_trans_v0` + `indexf_n` + `MIN_LEAST`
    （~40 行复杂索引机）。Lean 换成**偏离集非空**直证：
    ¬final 给 `u ∈ r` 使 `fList L u ≠ nextEl r u`；`u ≠ x`（marked 的
    `nextEl r x = fList x` 排除）；`indexfN` 把 u 写成 `(nextEl r)^[k] x`（k ≥ 1）；
    故 `k-1 ∈ {m | (nextEl r)^[m+2] x ≠ fList ((nextEl r)^[m+1] x)}`，该集非空
    ⇒ `Nat.sInf_mem` 得 `l'm ∈` 集 ⇒ `nextEl r (l'y) ≠ fList (l'y)`
    （`lYRepPower` 把 `l'y` 写成 `(nextEl r)^[l'm+1] x`）。**~65 行**；
  - ② `prevRNotEqF`：HOL 的 `sizel f` 三分叉换成 `l'p` 两支。
    `fList L z1 = z` ⇒ `z ∈ face z1` ⇒ 同面等表链 `face z1 = face z = face y`，
    故 `z1 ∈ f`、`nextEl f z1 = z`；`nextElIndexf`（|f| > 1 由 y,z 互异）
    给 `indexf z1 z f = 1`，`indexfYtransSucLp` 给 `indexf y z f = l'p+1`，
    `indexfAddRight` 合流得 `indexf y z1 f = l'p`：
    · `l'p = 0`：`indexfZeroEq` 给 `y = z1`、`indexfOne` 给 `fList y = z`、
      `nextElPrevElUniq` 给 `nextEl r y = z` ⇒ `nextEl r y = fList y`，撞 ①；
    · `l'p ≥ 1`：`indexfN + fListPowEqNextElPow` 给 `z1 = (fList)^[l'p] y`，
      `fListPowYtransNotMem` 在 j = l'p−1 处给其 ∉ r，撞 `z1 ∈ r`。
    **~75 行**。依赖方向与 HOL 一致（② 的 `l'p=0` 支吃 ①）。

  边界：本批只落两件；`uniqFstSplitNorm`（AQ1:1373）/ `f_lastSpine L split.1` /
  `aq3Concl` 全式仍在 E4d（缺口与修法见 DELIVERY 续 §2/§3）。

  纪律：零 sorry/admit/native_decide/axiom；主仓 tracked 零改动（经 patch 交付）。
-/
import Kepler.Text.TameSpine.JcajyduAqSplit1B

namespace Kepler.Text.TameSpine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts listPairs)
open Kepler.Graphs (fgraph between)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_mem_of_mem prevEl_mem_of_mem)

/-- **HOL `next_r_not_eq_f_v0`**（AQ1.hl:612）：`~(next_el r (l'y) = next_el f (l'y))`
（f = find_face L (l'y)）。 -/
theorem nextRNotEqF (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    nextEl r (lYSpine L r x) ≠ fList L (lYSpine L r x) := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hdev : ∃ u, u ∈ r ∧ fList L u ≠ nextEl r u := by
    by_contra h
    apply hf
    intro d hd
    by_contra hne
    exact h ⟨d, hd, hne⟩
  obtain ⟨u, hu, hune⟩ := hdev
  have hux : u ≠ x := by
    intro h
    subst h
    exact hune hnext.symm
  have hk : (nextEl r)^[indexf x u r] x = u := indexfN hxr hu hrnd
  have hkpos : 1 ≤ indexf x u r := by
    rcases Nat.eq_zero_or_pos (indexf x u r) with h0 | h1
    · exact absurd (indexfZeroEq (s := r) hxr hu h0).symm hux
    · exact h1
  have hmem : (indexf x u r - 1) ∈
      {m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)} := by
    rw [Set.mem_setOf_eq]
    have e1 : indexf x u r - 1 + 1 = indexf x u r := by omega
    have e2 : indexf x u r - 1 + 2 = indexf x u r + 1 := by omega
    rw [e2, e1, Function.iterate_succ_apply', hk]
    exact Ne.symm hune
  have hne : ({m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)}).Nonempty :=
    ⟨_, hmem⟩
  have hspec : (nextEl r)^[lMSpine L r x + 2] x
      ≠ fList L ((nextEl r)^[lMSpine L r x + 1] x) := by
    have h1 : lMSpine L r x
        = sInf {m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)} := rfl
    rw [h1]
    exact Nat.sInf_mem hne
  have hy : lYSpine L r x = (nextEl r)^[lMSpine L r x + 1] x :=
    lYRepPower L r x hnext.symm
  rw [hy]
  intro hcon
  exact hspec (by
    rw [show lMSpine L r x + 2 = (lMSpine L r x + 1) + 1 from by omega,
      Function.iterate_succ_apply']
    exact hcon)


/-- **HOL `prev_r_not_eq_f_v0`**（AQ1.hl:690）：`~(f_list L (prev_el r (l'z)) = l'z)`。 -/
theorem prevRNotEqF (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    fList L (prevEl r (lZSpine L N r x)) ≠ lZSpine L N r x := by
  intro hcon
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hyn : lYSpine L r x ∈ listOfDarts L := memYtransListOfDarts L hL hgn hm hf
  have hloop : loopListSpine L r := hm.1.2.1.2.2.2.1 r hm.1.2.2.1
  have hz1n : prevEl r (lZSpine L N r x) ∈ listOfDarts L := (hloop _ hz1r).1
  have hzn : lZSpine L N r x ∈ listOfDarts L := (hloop _ hzr).1
  have hyf : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L _).mpr hyn
  have hzf : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x) :=
    zMemFindFaceDarts L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L (lYSpine L r x)).Nodup := findFaceDarts_nodup hL.1 _
  have hzf1 : lZSpine L N r x ∈ findFaceDarts L (prevEl r (lZSpine L N r x)) := by
    have h1 : nextEl (findFaceDarts L (prevEl r (lZSpine L N r x)))
        (prevEl r (lZSpine L N r x))
        ∈ findFaceDarts L (prevEl r (lZSpine L N r x)) :=
      nextEl_mem_of_mem ((dart_in_face L _).mpr hz1n)
    rwa [show nextEl (findFaceDarts L (prevEl r (lZSpine L N r x)))
        (prevEl r (lZSpine L N r x)) = lZSpine L N r x from hcon] at h1
  have hcongr1 : findFaceDarts L (lZSpine L N r x)
      = findFaceDarts L (prevEl r (lZSpine L N r x)) :=
    findFaceDarts_congr_of_mem hL.1 hz1n hzf1
  have hcongr2 : findFaceDarts L (lZSpine L N r x) = findFaceDarts L (lYSpine L r x) :=
    findFaceDarts_congr_of_mem hL.1 hyn hzf
  have hfz1 : findFaceDarts L (prevEl r (lZSpine L N r x)) = findFaceDarts L (lYSpine L r x) :=
    hcongr1.symm.trans hcongr2
  have hz1f : prevEl r (lZSpine L N r x) ∈ findFaceDarts L (lYSpine L r x) := by
    have h1 : prevEl r (lZSpine L N r x)
        ∈ findFaceDarts L (prevEl r (lZSpine L N r x)) :=
      (dart_in_face L _).mpr hz1n
    rwa [hfz1] at h1
  have hnextf : nextEl (findFaceDarts L (lYSpine L r x)) (prevEl r (lZSpine L N r x))
      = lZSpine L N r x := by
    rw [← hfz1]
    exact hcon
  have hflen : 1 < (findFaceDarts L (lYSpine L r x)).length := by
    by_contra h
    have hy0 : (findFaceDarts L (lYSpine L r x)).idxOf (lYSpine L r x) = 0 := by
      have := List.idxOf_lt_length_iff.mpr hyf
      omega
    have hz0 : (findFaceDarts L (lYSpine L r x)).idxOf (lZSpine L N r x) = 0 := by
      have := List.idxOf_lt_length_iff.mpr hzf
      omega
    exact hyz ((List.idxOf_inj (l := findFaceDarts L (lYSpine L r x))
      (x := lYSpine L r x) (y := lZSpine L N r x) hyf).mp (hy0.trans hz0.symm))
  have hidx1 : indexf (prevEl r (lZSpine L N r x)) (lZSpine L N r x)
      (findFaceDarts L (lYSpine L r x)) = 1 :=
    nextElIndexf hz1f hzf hfnd hnextf hflen
  have hidxz : indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L (lYSpine L r x))
      = lPSpine L N r x + 1 := indexfYtransSucLp L hL hgn hunL hm hf
  have hle : indexf (prevEl r (lZSpine L N r x)) (lZSpine L N r x)
        (findFaceDarts L (lYSpine L r x))
      ≤ indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L (lYSpine L r x)) := by
    omega
  have hadd := indexfAddRight hyf hz1f hzf hle
  have hidxz1 : indexf (lYSpine L r x) (prevEl r (lZSpine L N r x))
        (findFaceDarts L (lYSpine L r x)) = lPSpine L N r x := by
    omega
  rcases Nat.eq_zero_or_pos (lPSpine L N r x) with h0 | hpos
  · have hyz1 : lYSpine L r x = prevEl r (lZSpine L N r x) := by
      apply indexfZeroEq hyf hz1f
      omega
    have hfl : fList L (lYSpine L r x) = lZSpine L N r x := by
      have h1 : indexf (lYSpine L r x) (lZSpine L N r x)
          (findFaceDarts L (lYSpine L r x)) = 1 := by omega
      exact indexfOne hyf hzf hfnd h1
    have hnr : nextEl r (lYSpine L r x) = lZSpine L N r x := by
      rw [hyz1]
      exact nextElPrevElUniq hrnd _
    exact nextRNotEqF L hL hgn hunL hm hf (hnr.trans hfl.symm)
  · have hpow : (fList L)^[lPSpine L N r x] (lYSpine L r x)
        = prevEl r (lZSpine L N r x) := by
      rw [fListPowEqNextElPow L hL (lYSpine L r x) hyf, ← hidxz1]
      exact indexfN hyf hz1f hfnd
    have hnot := fListPowYtransNotMem L hL hm (lPSpine L N r x - 1) (by omega)
    exact hnot (by
      rw [show lPSpine L N r x - 1 + 1 = lPSpine L N r x from by omega, hpow]
      exact hz1r)

end Kepler.Text.TameSpine

#print axioms Kepler.Text.TameSpine.nextRNotEqF
#print axioms Kepler.Text.TameSpine.prevRNotEqF
