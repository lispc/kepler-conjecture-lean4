/-
  Kepler.Text.Reduction5Ml1W5Spine — 8b W5a/T1+T2 的 spine 世界证体
  （HOL DIOWAAS.hl:33–:200 / RYIUUVK.hl:35–:170）。

  件目：lengYtransWConstSpine / lengYtransZtransConstSpine / lengZtransWConstSpine
  （r↔rtrans 索引转移包）+ diowaasRSpine / ryiuuvkRSpine（r 侧两不等式）。
  路线：HOL 证体逐语句重推，全部原语用 spine 塔层形（Pnxvwfs/Pbflhet/Pwssrat）。
  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动。
-/
import Kepler.Text.TameSpine.Reduction3Pnxvwfs
import Kepler.Text.TameSpine.Reduction3Pbflhet2
import Kepler.Text.TameSpine.Reduction3Pbflhet3
import Kepler.Text.TameSpine.Reduction3Pbflhet4
import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl fList eList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)

/-- **T1-a（HOL `DIOWAAS.leng_ytrans_ztrans_const`，DIOWAAS.hl:33–83）**：
`indexf (l'y(i)) (l'z(i)) r_i = indexf (l'y(i)) (l'z(i)) r`。 -/
theorem lengYtransZtransConstSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    indexf (ytransSpine L N r x i) (ztransSpine L N r x i)
        (rtransSpine L N r x i)
      = indexf (ytransSpine L N r x i) (ztransSpine L N r x i) r := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    rfl
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hfj : ¬ finalListSpine L (rtransSpine L N r x j) :=
      finalListInductSpine L N r x j hf
    set f := findFaceDarts L x with hfdef
    set w := nextEl f x with hwdef
    have hfind : findFaceDarts L x = f := hfdef.symm
    have hw : nextEl f x = w := hwdef.symm
    have hy : ytransSpine L N r x (j + 1) ∈ rtransSpine L N r x j :=
      ytransInSucSpine L hL hta hgn hunL hm j hf hfind hw
    have hz : ztransSpine L N r x (j + 1) ∈ rtransSpine L N r x j :=
      ztranSucInRtransSpine L hL hta hgn hunL hm j hf hfind hw
    have h1 : indexf (ztransSpine L N r x j) (ytransSpine L N r x (j + 1))
          (rtransSpine L N r x j)
        < indexf (ztransSpine L N r x j) (ztransSpine L N r x (j + 1))
          (rtransSpine L N r x j) :=
      ytranSucBetwnZZSucSpine L hL hta hgn hunL hm j hf hfind hw
    have h2 : indexf (ztransSpine L N r x j) (ztransSpine L N r x (j + 1))
          (rtransSpine L N r x j)
        < indexf (ztransSpine L N r x j) w (rtransSpine L N r x j) :=
      ztransSucInZtranWSpineClosed L hL hta hgn hunL hm j hf hfind hw
    have h3 : indexf (ztransSpine L N r x j) w (rtransSpine L N r x j)
        ≤ indexf (ztransSpine L N r x j) (ytransSpine L N r x 0)
          (rtransSpine L N r x j) :=
      (wBetwnZtransYtran0Spine L hL hta hgn hunL hm j hfj hfind hw).1
    have hpa := pbflhetAllSpine L hL hta hgn hunL hm j hfj hz hy
      (le_of_lt h2 |>.trans h3) (le_of_lt h1)
    have hpa0 := hpa 0 (Nat.zero_le j)
    have hconst0 : indexf (ytransSpine L N r x (j + 1))
          (ztransSpine L N r x (j + 1)) r
        = indexf (ytransSpine L N r x (j + 1))
          (ztransSpine L N r x (j + 1)) (rtransSpine L N r x j) :=
      hpa0.2.2.2.2
    have hy2 : ytransSpine L N r x (j + 1) ∈ rtransSpine L N r x (j + 1) :=
      ytransMemRtrans L hL hgn (aqiunpp3 L hL (j + 1) hta hgn hm) hf
    have hz2 : ztransSpine L N r x (j + 1) ∈ rtransSpine L N r x (j + 1) :=
      memZtransRtransSpine L hL hgn hunL hta hm (j + 1) hf
    have htr := transIndexfSucSpine L hL hta hgn hunL hm j hfj hz hy hz2 hy2
      (le_of_lt h1)
    exact htr.symm.trans hconst0.symm

/-- **T1-b（HOL `DIOWAAS.leng_ytrans_w_const`，DIOWAAS.hl:85–140）**：
`indexf (l'y(i)) w r_i = indexf (l'y(i)) w r`（`w = next_el (find_face L x) x`）。 -/
theorem lengYtransWConstSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {w : ℕ × ℕ} (hw : nextEl (findFaceDarts L x) x = w) :
    indexf (ytransSpine L N r x i) w (rtransSpine L N r x i)
      = indexf (ytransSpine L N r x i) w r := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    rfl
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hfj : ¬ finalListSpine L (rtransSpine L N r x j) :=
      finalListInductSpine L N r x j hf
    set f := findFaceDarts L x with hfdef
    have hfind : findFaceDarts L x = f := hfdef.symm
    have hw' : nextEl f x = w := by rw [hfdef]; exact hw
    have hy : ytransSpine L N r x (j + 1) ∈ rtransSpine L N r x j :=
      ytransInSucSpine L hL hta hgn hunL hm j hf hfind hw'
    have hz : ztransSpine L N r x (j + 1) ∈ rtransSpine L N r x j :=
      ztranSucInRtransSpine L hL hta hgn hunL hm j hf hfind hw'
    have h1 : indexf (ztransSpine L N r x j) (ytransSpine L N r x (j + 1))
          (rtransSpine L N r x j)
        < indexf (ztransSpine L N r x j) (ztransSpine L N r x (j + 1))
          (rtransSpine L N r x j) :=
      ytranSucBetwnZZSucSpine L hL hta hgn hunL hm j hf hfind hw'
    have h2 : indexf (ztransSpine L N r x j) (ztransSpine L N r x (j + 1))
          (rtransSpine L N r x j)
        < indexf (ztransSpine L N r x j) w (rtransSpine L N r x j) :=
      ztransSucInZtranWSpineClosed L hL hta hgn hunL hm j hf hfind hw'
    have h3 : indexf (ztransSpine L N r x j) w (rtransSpine L N r x j)
        ≤ indexf (ztransSpine L N r x j) (ytransSpine L N r x 0)
          (rtransSpine L N r x j) :=
      (wBetwnZtransYtran0Spine L hL hta hgn hunL hm j hfj hfind hw').1
    have hwr : w ∈ rtransSpine L N r x j := by
      have h := nextMarkMemRTransSpine L hL hgn hta hm j
      rwa [hw] at h
    have hpa := pbflhetAllSpine L hL hta hgn hunL hm j hfj hwr hy
      h3 (le_of_lt h1 |>.trans (le_of_lt h2))
    have hpa0 := hpa 0 (Nat.zero_le j)
    have hconst0 : indexf (ytransSpine L N r x (j + 1)) w r
        = indexf (ytransSpine L N r x (j + 1)) w (rtransSpine L N r x j) :=
      hpa0.2.2.2.2
    have hy2 : ytransSpine L N r x (j + 1) ∈ rtransSpine L N r x (j + 1) :=
      ytransMemRtrans L hL hgn (aqiunpp3 L hL (j + 1) hta hgn hm) hf
    have hw2 : w ∈ rtransSpine L N r x (j + 1) := by
      have h := nextMarkMemRTransSpine L hL hgn hta hm (j + 1)
      rwa [hw] at h
    have htr := transIndexfSucSpine L hL hta hgn hunL hm j hfj hwr hy hw2 hy2
      (le_of_lt h1 |>.trans (le_of_lt h2))
    exact htr.symm.trans hconst0.symm

/-- **T1-c（HOL `RYIUUVK.leng_ztrans_w_const`，RYIUUVK.hl:35–90）**：
`indexf (l'z(i)) w r_i = indexf (l'z(i)) w r`（`w = next_el (find_face L x) x`）。 -/
theorem lengZtransWConstSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {w : ℕ × ℕ} (hw : nextEl (findFaceDarts L x) x = w) :
    indexf (ztransSpine L N r x i) w (rtransSpine L N r x i)
      = indexf (ztransSpine L N r x i) w r := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    rfl
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hfj : ¬ finalListSpine L (rtransSpine L N r x j) :=
      finalListInductSpine L N r x j hf
    set f := findFaceDarts L x with hfdef
    have hfind : findFaceDarts L x = f := hfdef.symm
    have hw' : nextEl f x = w := by rw [hfdef]; exact hw
    have hz : ztransSpine L N r x (j + 1) ∈ rtransSpine L N r x j :=
      ztranSucInRtransSpine L hL hta hgn hunL hm j hf hfind hw'
    have h1 : indexf (ztransSpine L N r x j) (ytransSpine L N r x (j + 1))
          (rtransSpine L N r x j)
        < indexf (ztransSpine L N r x j) (ztransSpine L N r x (j + 1))
          (rtransSpine L N r x j) :=
      ytranSucBetwnZZSucSpine L hL hta hgn hunL hm j hf hfind hw'
    have h2 : indexf (ztransSpine L N r x j) (ztransSpine L N r x (j + 1))
          (rtransSpine L N r x j)
        < indexf (ztransSpine L N r x j) w (rtransSpine L N r x j) :=
      ztransSucInZtranWSpineClosed L hL hta hgn hunL hm j hf hfind hw'
    have h3 : indexf (ztransSpine L N r x j) w (rtransSpine L N r x j)
        ≤ indexf (ztransSpine L N r x j) (ytransSpine L N r x 0)
          (rtransSpine L N r x j) :=
      (wBetwnZtransYtran0Spine L hL hta hgn hunL hm j hfj hfind hw').1
    have hwr : w ∈ rtransSpine L N r x j := by
      have h := nextMarkMemRTransSpine L hL hgn hta hm j
      rwa [hw] at h
    have hpa := pbflhetAllSpine L hL hta hgn hunL hm j hfj hwr hz
      h3 (le_of_lt h2)
    have hpa0 := hpa 0 (Nat.zero_le j)
    have hconst0 : indexf (ztransSpine L N r x (j + 1)) w r
        = indexf (ztransSpine L N r x (j + 1)) w (rtransSpine L N r x j) :=
      hpa0.2.2.2.2
    have hz2 : ztransSpine L N r x (j + 1) ∈ rtransSpine L N r x (j + 1) :=
      memZtransRtransSpine L hL hgn hunL hta hm (j + 1) hf
    have hw2 : w ∈ rtransSpine L N r x (j + 1) := by
      have h := nextMarkMemRTransSpine L hL hgn hta hm (j + 1)
      rwa [hw] at h
    have htr := transIndexfSucSpine L hL hta hgn hunL hm j hfj hwr hz hw2 hz2
      (le_of_lt h2)
    exact htr.symm.trans hconst0.symm

/-- **T2-a（HOL `DIOWAAS`，DIOWAAS.hl:142–:200）**：
r 侧 `indexf w (l'y(i)) r < indexf w (l'z(i)) r`（`w = next_el (find_face L x) x`）。 -/
theorem diowaasRSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {w : ℕ × ℕ} (hw : nextEl (findFaceDarts L x) x = w) :
    indexf w (ytransSpine L N r x i) r < indexf w (ztransSpine L N r x i) r := by
  have h0 : indexf w (ytransSpine L N r x i) (rtransSpine L N r x i)
      < indexf w (ztransSpine L N r x i) (rtransSpine L N r x i) :=
    indexfYLeZInRSpine L hL hta hgn hm i hf (f := findFaceDarts L x) rfl hw
  have hwr : w ∈ rtransSpine L N r x i := by
    have h := nextMarkMemRTransSpine L hL hgn hta hm i
    rwa [hw] at h
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hyr : ytransSpine L N r x i ∈ rtransSpine L N r x i :=
    ytransMemRtrans L hL hgn hmr hf
  have hzr : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hf
  by_cases hwy : w = ytransSpine L N r x i
  · -- w = y：0 < y→z（r 上）
    have hyr0 : ytransSpine L N r x i ∈ r :=
      pnxvwfs1Spine L hL hta hgn hunL hm i hf
    rw [hwy]
    have h0' : 0 < indexf (ytransSpine L N r x i) (ztransSpine L N r x i)
        (rtransSpine L N r x i) := by
      rw [hwy] at h0
      rwa [indexfRefl hyr] at h0
    have hc := lengYtransZtransConstSpine L hL hta hgn hunL hm i hf
    rw [hc] at h0'
    rw [indexfRefl (s := r) hyr0]
    exact h0'
  · by_cases hwz : w = ztransSpine L N r x i
    · -- w = z：h0 直接矛盾（z→y < 0）
      rw [hwz] at h0
      rw [indexfRefl hzr] at h0
      exact absurd h0 (Nat.not_lt_zero _)
    · -- 其余：antisym 双发 + T1 折回 + add_left
      have hzy : ztransSpine L N r x i ≠ ytransSpine L N r x i :=
        fun h => hqymrtx3List L hL hgn hunL hmr hf h.symm
      have hA1 := indexfAntisym hwr hyr hwy
      have hA2 := indexfAntisym hwr hzr hwz
      have hA3 := indexfAddLeft hwr hyr hzr (le_of_lt h0)
      have hL1 := lengYtransWConstSpine L hL hta hgn hunL hm i hf hw
      have hL2 := lengZtransWConstSpine L hL hta hgn hunL hm i hf hw
      have hL3 := lengYtransZtransConstSpine L hL hta hgn hunL hm i hf
      have hyr0 : ytransSpine L N r x i ∈ r :=
        pnxvwfs1Spine L hL hta hgn hunL hm i hf
      have hzr0 : ztransSpine L N r x i ∈ r :=
        pnxvwfs2Spine L hL hta hgn hunL hm i hf
      have hwr0 : w ∈ r := by
        have h := nextMarkMemRTransSpine L hL hgn hta hm 0
        rwa [hw] at h
      have hB1 := indexfAntisym hwr0 hyr0 hwy
      have hB2 := indexfAntisym hwr0 hzr0 hwz
      have hpos : 0 < indexf (ytransSpine L N r x i) (ztransSpine L N r x i) r := by
        by_contra hcon
        have hzero : indexf (ytransSpine L N r x i) (ztransSpine L N r x i) r = 0 := by
          omega
        exact hzy (indexfZeroEq hyr0 hzr0 hzero).symm
      rw [← hL1] at hB1
      rw [← hL2] at hB2
      rw [← hL3] at hpos
      omega

/-- **T2-b（HOL `RYIUUVK`，RYIUUVK.hl:92–:170）**：
r 侧 `indexf w (l'z(i)) r ≤ indexf w (l'y(i+1)) r`（`w = next_el (find_face L x) x`）。 -/
theorem ryiuuvkRSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {w : ℕ × ℕ} (hw : nextEl (findFaceDarts L x) x = w) :
    indexf w (ztransSpine L N r x i) r
      ≤ indexf w (ytransSpine L N r x (i + 1)) r := by
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    finalListInductSpine L N r x i hf
  set f := findFaceDarts L x with hfdef
  have hfind : findFaceDarts L x = f := hfdef.symm
  have hw' : nextEl f x = w := by rw [hfdef]; exact hw
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
  have hws : w ∈ rtransSpine L N r x i := by
    have h := nextMarkMemRTransSpine L hL hgn hta hm i
    rwa [hw] at h
  have hzs : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hfi
  have hys : ytransSpine L N r x (i + 1) ∈ rtransSpine L N r x i :=
    ytransInSucSpine L hL hta hgn hunL hm i hf hfind hw'
  have h1 : indexf (ztransSpine L N r x i) (ytransSpine L N r x (i + 1))
        (rtransSpine L N r x i)
      < indexf (ztransSpine L N r x i) (ztransSpine L N r x (i + 1))
        (rtransSpine L N r x i) :=
    ytranSucBetwnZZSucSpine L hL hta hgn hunL hm i hf hfind hw'
  have h2 : indexf (ztransSpine L N r x i) (ztransSpine L N r x (i + 1))
        (rtransSpine L N r x i)
      < indexf (ztransSpine L N r x i) w (rtransSpine L N r x i) :=
    ztransSucInZtranWSpineClosed L hL hta hgn hunL hm i hf hfind hw'
  by_cases hwy : w = ytransSpine L N r x (i + 1)
  · rw [hwy] at h2
    omega
  · by_cases hwz : w = ztransSpine L N r x i
    · have hzr0 : ztransSpine L N r x i ∈ r :=
        pnxvwfs2Spine L hL hta hgn hunL hm i hfi
      rw [hwz]
      rw [indexfRefl (s := r) hzr0]
      exact Nat.zero_le _
    · -- 其余：转移链（trans@i + T1），目标折回 r_i 后由 A3 收口
      have hA1 := indexfAntisym hws hzs hwz
      have hA2 := indexfAntisym hws hys hwy
      have hA3 := indexfAddLeft hzs hys hws (le_of_lt h1 |>.trans (le_of_lt h2))
      have hws2 : w ∈ rtransSpine L N r x (i + 1) := by
        have h := nextMarkMemRTransSpine L hL hgn hta hm (i + 1)
        rwa [hw] at h
      have hys2 : ytransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
        ytransMemRtrans L hL hgn hmr1 hf
      have htr2 := transIndexfSucSpine L hL hta hgn hunL hm i hfi hws hys hws2 hys2
        (le_of_lt h1 |>.trans (le_of_lt h2))
      have hL1 := lengZtransWConstSpine L hL hta hgn hunL hm i hfi hw
      have hL2 := lengYtransWConstSpine L hL hta hgn hunL hm (i + 1) hf hw
      have hzWr : indexf (ztransSpine L N r x i) w r
          = indexf (ztransSpine L N r x i) w (rtransSpine L N r x i) := hL1.symm
      have hysWr : indexf (ytransSpine L N r x (i + 1)) w r
          = indexf (ytransSpine L N r x (i + 1)) w (rtransSpine L N r x i) := by
        rw [← hL2, ← htr2]
      have hwr0 : w ∈ r := by
        have h := nextMarkMemRTransSpine L hL hgn hta hm 0
        rwa [hw] at h
      have hzr0 : ztransSpine L N r x i ∈ r :=
        pnxvwfs2Spine L hL hta hgn hunL hm i hfi
      have hyr0 : ytransSpine L N r x (i + 1) ∈ r :=
        pnxvwfs1Spine L hL hta hgn hunL hm (i + 1) hf
      have hB1 := indexfAntisym hwr0 hzr0 hwz
      have hB2 := indexfAntisym hwr0 hyr0 hwy
      have hle : indexf (ytransSpine L N r x (i + 1)) w r
          ≤ indexf (ztransSpine L N r x i) w r := by
        rw [hysWr, hzWr]
        omega
      omega

end Kepler.Text.TameSpine

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.TameSpine.lengYtransZtransConstSpine
#print axioms Kepler.Text.TameSpine.lengYtransWConstSpine
#print axioms Kepler.Text.TameSpine.lengZtransWConstSpine
#print axioms Kepler.Text.TameSpine.diowaasRSpine
#print axioms Kepler.Text.TameSpine.ryiuuvkRSpine
