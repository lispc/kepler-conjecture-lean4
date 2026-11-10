/-
  Kepler.Text.TameSpine.Reduction3KbwpbhqYtransConst — tame-corr nb8：
  KBWPBHQ 章 next_ytrans_const 支件链五件（波 B1；KBWPBHQ1 ⟹ 向上游）。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ ① `ltFromYSpine`（KBWPBHQ.hl:90-144
  │    lt_from_y_indexf_in_rtrans_suc_not_rtrans）：¬final(i+1) ∧ d ∈ r₂
  │    ∧ d ∉ r₁ ⇒ indexf (l'y(i+1)) w r₂ < indexf (l'y(i+1)) d r₂。
  │    证（HOL 同构）：lt_indexf_in_rtrans_suc_not_rtrans（nb4）+
  │    indexf_add_left[w;d;ys;r₂] + d ≠ ys / w ≠ ys（自反相抵）+
  │    indexf_antisym×2 + 相等支 indexf_n×2 ⟹ d = w ∈ r₁ 矛盾。
  │ ② `memFromYSpine`（KBWPBHQ.hl:148-159
  │    mem_from_y_indexf_in_rtrans_suc_not_rtrans）：① 的逆否。
  │ ③ `indexfYtransLeDConstSpine`（KBWPBHQ.hl:163-262
  │    indexf_ytrans_le_d_const，100 HOL 行）：¬final(i) ∧ d ∈ rᵢ ∧
  │    indexf (l'y(i)) d rᵢ ≤ indexf (l'y(i)) w rᵢ ⇒ MEM d r ∧
  │    indexf (l'y(i)) d rᵢ = indexf (l'y(i)) d r。
  │    证（HOL 同构）：i = 0 定义级；i = j+1：② 给 d ∈ r_j；二分
  │    z→d < z→yᵢ（r_j 上）——A 支 trans_indexf_suc 双实例 +
  │    indexf_add_left×4 omega 反证；B 支 trans_indexf_suc 双实例 +
  │    indexf_add_left×2 ⟹ z→d ≤ z→l'y(0) ⟹ PBFLHET_ALL @d1:=yᵢ、t:=0。
  │ ④ `nextEqRtransRSpine`（KBWPBHQ.hl:268-307 next_eq_rtrans_r）：
  │    ¬final(i) ∧ n ≤ indexf (l'y(i)) w rᵢ ⇒
  │    (next_el rᵢ)^n (l'y(i)) = (next_el r)^n (l'y(i))。
  │    证 = MEM_POWER_NEXT_EL + next_eln_indexf（rᵢ）+ ③ + PNXVWFS1 +
  │    indexf_n（r）。
  │ ⑤ `nextYtransConstSpine`（KBWPBHQ.hl:309-351 next_ytrans_const）：
  │    ¬final(i) ⇒ next_el rᵢ (l'y(i)) = next_el r (l'y(i))。
  │    i = 0 定义级；i > 0：indexf yᵢ w rᵢ ≥ 1 支 = ④ @n:=1；= 0 支
  │    （yᵢ = w）反证——**路线差异记档**：HOL 引 Ryiuuvk.RYIUUVK 与
  │    Diowaas.DIOWAAS（r 侧 index 形，两章 Lean 侧零命中），本件取其
  │    f 侧孪生 QCDVKEA@(i−1)（w→z f ≤ w→yᵢ f）+ PPLHULJ@(i−1)
  │    （w→y f < w→z f）得 0 < w→yᵢ f，与 yᵢ = w（indexf_refl）矛盾；
  │    结构同构（「z(i−1) ≤ y(i)」与「y(i−1) < z(i−1)」两条不等式相抵）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ ltIndexfInRtransSucNotRtrans / ytransMemRtrans / nextMarkMemRTransSpine
  │ / finalListInductSpine / ytransInSucSpine / ytranSucBetwnZZSucSpine /
  │ ztransSucInZtranWSpineClosed / wBetwnZtransYtran0Spine /
  │ ztransInSucSpine / memZtransRtransSpine / transIndexfSucSpine /
  │ pbflhetAllSpine / pnxvwfs1Spine / qcdvkeaTowerSpine / pplhuljV0 /
  │ aq10_memNextMarkInface / TameList3 indexf 族 / memPowerNextEl）
  │ 同世界零混合；零 Dart 载体件。默认心跳、linter 全开。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Pnxvwfs

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl)

/-! ## §1 lt_from_y / mem_from_y（KBWPBHQ.hl:90-159） -/

/-- **HOL `Kbwpbhq.lt_from_y_indexf_in_rtrans_suc_not_rtrans`**
（KBWPBHQ.hl:90-144）塔层 i 形：`¬final(i+1) ∧ d ∈ r₂ ∧ d ∉ r₁ ⇒
indexf (l'y(i+1)) w r₂ < indexf (l'y(i+1)) d r₂`。
证（HOL 同构）：nb4 lt_indexf（w→d < w→ys，r₂）+ indexf_add_left[w;d;ys]
+ indexf_antisym×2（d ≠ ys、w ≠ ys 由自反相抵）+ 相等支 indexf_n×2
⟹ d = w ∈ r₁ 矛盾。 -/
theorem ltFromYSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hd0 : d ∉ rtransSpine L N r x i) :
    indexf (ytransSpine L N r x (i + 1)) w (rtransSpine L N r x (i + 1))
      < indexf (ytransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1)) := by
  have hlt := ltIndexfInRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw
    hd1 hd0
  have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
  have hys : ytransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
    ytransMemRtrans L hL hgn hmr1 hf
  have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
  have hwrs : w ∈ rtransSpine L N r x (i + 1) := by
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm (i + 1)
  have hwri : w ∈ rtransSpine L N r x i := by
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm i
  have hrsnd : (rtransSpine L N r x (i + 1)).Nodup :=
    (normalListUniqNonnil hmr1.1.2.1 hmr1.1.2.2.1).1
  have hA := indexfAddLeft hwrs hd1 hys (Nat.le_of_lt hlt)
  have hdne : d ≠ ytransSpine L N r x (i + 1) := by
    intro h
    rw [h] at hlt
    exact lt_irrefl _ hlt
  have hwne : w ≠ ytransSpine L N r x (i + 1) := by
    intro h
    have h0 : indexf w (ytransSpine L N r x (i + 1))
        (rtransSpine L N r x (i + 1)) = 0 := by
      rw [h]
      exact indexfRefl hys
    omega
  have han1 := indexfAntisym hd1 hys hdne
  have han2 := indexfAntisym hwrs hys hwne
  by_contra hcon
  -- 相等支：ys→w = ys→d ⟹ w = d（indexf_n×2）⟹ d ∈ r₁ 矛盾
  have heq : indexf (ytransSpine L N r x (i + 1)) w (rtransSpine L N r x (i + 1))
      = indexf (ytransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1)) := by
    omega
  have e1 := indexfN hys hwrs hrsnd
  have e2 := indexfN hys hd1 hrsnd
  rw [heq] at e1
  have hdw : d = w := e2.symm.trans e1
  rw [hdw] at hd0
  exact hd0 hwri

/-- **HOL `Kbwpbhq.mem_from_y_indexf_in_rtrans_suc_not_rtrans`**
（KBWPBHQ.hl:148-159）塔层 i 形：`¬final(i+1) ∧ d ∈ r₂ ∧
indexf (l'y(i+1)) d r₂ ≤ indexf (l'y(i+1)) w r₂ ⇒ MEM d r₁`。
上件逆否。 -/
theorem memFromYSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hle : indexf (ytransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))
      ≤ indexf (ytransSpine L N r x (i + 1)) w (rtransSpine L N r x (i + 1))) :
    d ∈ rtransSpine L N r x i := by
  by_contra hnot
  have h := ltFromYSpine L hL hta hgn hunL hm i hf hfind hw hd1 hnot
  omega

/-! ## §2 indexf_ytrans_le_d_const（KBWPBHQ.hl:163-262） -/

/-- **HOL `Kbwpbhq.indexf_ytrans_le_d_const`**（KBWPBHQ.hl:163-262）塔层
i 形：`¬final(i) ∧ d ∈ rᵢ ∧ indexf (l'y(i)) d rᵢ ≤ indexf (l'y(i)) w rᵢ ⇒
MEM d r ∧ indexf (l'y(i)) d rᵢ = indexf (l'y(i)) d r`。
证（HOL 同构）：i = 0 定义级；i = j+1 见文件头 ③。 -/
theorem indexfYtransLeDConstSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x i)
    (hle : indexf (ytransSpine L N r x i) d (rtransSpine L N r x i)
      ≤ indexf (ytransSpine L N r x i) w (rtransSpine L N r x i)) :
    d ∈ r ∧ indexf (ytransSpine L N r x i) d (rtransSpine L N r x i)
      = indexf (ytransSpine L N r x i) d r := by
  cases i with
  | zero =>
    rw [show rtransSpine L N r x 0 = r from rfl] at hd ⊢
    exact ⟨hd, rfl⟩
  | succ j =>
    have hfj : ¬ finalListSpine L (rtransSpine L N r x j) :=
      finalListInductSpine L N r x j hf
    have hmr1 := aqiunpp3 L hL (j + 1) hta hgn hm
    have hyir1 : ytransSpine L N r x (j + 1) ∈ rtransSpine L N r x j :=
      ytransInSucSpine L hL hta hgn hunL hm j hf hfind hw
    have hyiri : ytransSpine L N r x (j + 1) ∈ rtransSpine L N r x (j + 1) :=
      ytransMemRtrans L hL hgn hmr1 hf
    have hB := ytranSucBetwnZZSucSpine L hL hta hgn hunL hm j hf hfind hw
    have hZ := ztransSucInZtranWSpineClosed L hL hta hgn hunL hm j hf hfind hw
    obtain ⟨hW1, -⟩ := wBetwnZtransYtran0Spine L hL hta hgn hunL hm j hfj
      hfind hw
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    have hwr1 : w ∈ rtransSpine L N r x j := by
      rw [← hw']
      exact nextMarkMemRTransSpine L hL hgn hta hm j
    have hwri : w ∈ rtransSpine L N r x (j + 1) := by
      rw [← hw']
      exact nextMarkMemRTransSpine L hL hgn hta hm (j + 1)
    have hzr1 : ztransSpine L N r x j ∈ rtransSpine L N r x j :=
      memZtransRtransSpine L hL hgn hunL hta hm j hfj
    -- mem_from_y：d ∈ r_j
    have hdr1 : d ∈ rtransSpine L N r x j :=
      memFromYSpine L hL hta hgn hunL hm j hf hfind hw hd hle
    -- trans (yᵢ, w)：界 z→yᵢ ≤ z→w（r_j 上）
    have hT2 := transIndexfSucSpine L hL hta hgn hunL hm j hfj hwr1 hyir1
      hwri hyiri (by omega)
    have hA3 := indexfAddLeft hzr1 hyir1 hwr1 (by omega)
    by_cases hc : indexf (ztransSpine L N r x j) d (rtransSpine L N r x j)
        < indexf (ztransSpine L N r x j) (ytransSpine L N r x (j + 1))
          (rtransSpine L N r x j)
    · -- A 支（z→d < z→yᵢ）：反证
      exfalso
      have hT1 := transIndexfSucSpine L hL hta hgn hunL hm j hfj hwr1 hdr1
        hwri hd (by omega)
      have hA1 := indexfAddLeft hzr1 hdr1 hyir1 (by omega)
      have hA2 := indexfAddLeft hzr1 hdr1 hwr1 (by omega)
      have hA4 := indexfAddLeft hyiri hd hwri hle
      omega
    · -- B 支（z→yᵢ ≤ z→d）：PBFLHET_ALL @d1 := yᵢ
      have hT3 := transIndexfSucSpine L hL hta hgn hunL hm j hfj hdr1 hyir1
        hd hyiri (by omega)
      have hA5 := indexfAddLeft hzr1 hyir1 hdr1 (by omega)
      have hzd : indexf (ztransSpine L N r x j) d (rtransSpine L N r x j)
          ≤ indexf (ztransSpine L N r x j) (ytransSpine L N r x 0)
            (rtransSpine L N r x j) := by omega
      obtain ⟨hdr, -, -, -, heq0⟩ :=
        pbflhetAllSpine L hL hta hgn hunL hm j hfj hdr1 hyir1 hzd (by omega)
          0 (Nat.zero_le j)
      rw [show rtransSpine L N r x 0 = r from rfl] at hdr heq0
      exact ⟨hdr, by omega⟩

/-! ## §3 next_eq_rtrans_r + next_ytrans_const（KBWPBHQ.hl:268-351） -/

/-- **HOL `Kbwpbhq.next_eq_rtrans_r`**（KBWPBHQ.hl:268-307）塔层 i 形：
`¬final(i) ∧ n ≤ indexf (l'y(i)) w rᵢ ⇒
(next_el rᵢ)^n (l'y(i)) = (next_el r)^n (l'y(i))`。
证 = MEM_POWER_NEXT_EL + next_eln_indexf（rᵢ 上 yᵢ→d = n）+
indexf_ytrans_le_d_const（d ∈ r ∧ index 不变）+ PNXVWFS1（yᵢ ∈ r）+
indexf_n（r 上）。 -/
theorem nextEqRtransRSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) {n : ℕ}
    (hn : n ≤ indexf (ytransSpine L N r x i) w (rtransSpine L N r x i)) :
    (nextEl (rtransSpine L N r x i))^[n] (ytransSpine L N r x i)
      = (nextEl r)^[n] (ytransSpine L N r x i) := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hyri : ytransSpine L N r x i ∈ rtransSpine L N r x i :=
    ytransMemRtrans L hL hgn hmr hf
  have hrind : (rtransSpine L N r x i).Nodup :=
    (normalListUniqNonnil hmr.1.2.1 hmr.1.2.2.1).1
  obtain ⟨d, hd⟩ : ∃ d, d = (nextEl (rtransSpine L N r x i))^[n]
      (ytransSpine L N r x i) := ⟨_, rfl⟩
  have hdri : d ∈ rtransSpine L N r x i := by
    rw [hd]
    exact memPowerNextEl hyri n
  have hwri : w ∈ rtransSpine L N r x i := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm i
  have hlt := indexfLtSizel hyri hwri
  have hid : indexf (ytransSpine L N r x i) d (rtransSpine L N r x i) = n :=
    nextElnIndexf hyri hdri hrind hd.symm (by omega)
  obtain ⟨hdr, heq⟩ := indexfYtransLeDConstSpine L hL hta hgn hunL hm i hf
    hfind hw hdri (by omega)
  have hyr : ytransSpine L N r x i ∈ r :=
    pnxvwfs1Spine L hL hta hgn hunL hm i hf
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hfin := indexfN hyr hdr hrnd
  have hidx : indexf (ytransSpine L N r x i) d r = n := by omega
  rw [hidx] at hfin
  rw [← hd]
  exact hfin.symm

/-- **HOL `Kbwpbhq.next_ytrans_const`**（KBWPBHQ.hl:309-351）塔层 i 形：
`¬final(i) ⇒ next_el rᵢ (l'y(i)) = next_el r (l'y(i))`。
i = 0 定义级；i > 0：yᵢ→w ≥ 1 支 = next_eq_rtrans_r @n:=1；= 0 支
（yᵢ = w）反证——HOL 引 RYIUUVK/DIOWAAS（r 侧，Lean 零命中），此处取
f 侧孪生 QCDVKEA@(i−1) + PPLHULJ@(i−1)（路线差异见文件头 ⑤）。 -/
theorem nextYtransConstSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    nextEl (rtransSpine L N r x i) (ytransSpine L N r x i)
      = nextEl r (ytransSpine L N r x i) := by
  cases i with
  | zero =>
    rw [show rtransSpine L N r x 0 = r from rfl]
  | succ j =>
    obtain ⟨w, hw⟩ : ∃ w, nextEl (findFaceDarts L x) x = w := ⟨_, rfl⟩
    have hmr1 := aqiunpp3 L hL (j + 1) hta hgn hm
    have hyi : ytransSpine L N r x (j + 1) ∈ rtransSpine L N r x (j + 1) :=
      ytransMemRtrans L hL hgn hmr1 hf
    have hwri : w ∈ rtransSpine L N r x (j + 1) := by
      rw [← hw]
      exact nextMarkMemRTransSpine L hL hgn hta hm (j + 1)
    by_cases h0 : indexf (ytransSpine L N r x (j + 1)) w
        (rtransSpine L N r x (j + 1)) = 0
    · -- yᵢ = w 支：f 侧孪生反证
      exfalso
      have hyw : ytransSpine L N r x (j + 1) = w := indexfZeroEq hyi hwri h0
      have hfj : ¬ finalListSpine L (rtransSpine L N r x j) :=
        finalListInductSpine L N r x j hf
      have hQ := qcdvkeaTowerSpine L hL hta hgn hm j hf rfl hw
      obtain ⟨-, -, hlt0⟩ :=
        pplhuljV0 L hL hgn hunL (aqiunpp3 L hL j hta hgn hm) hfj
      rw [hw] at hlt0
      have hlt : indexf w (ytransSpine L N r x j) (findFaceDarts L x)
          < indexf w (ztransSpine L N r x j) (findFaceDarts L x) := hlt0
      have hwf : w ∈ findFaceDarts L x := by
        rw [← hw]
        exact aq10_memNextMarkInface L hL hgn hm
      have h00 : indexf w (ytransSpine L N r x (j + 1)) (findFaceDarts L x)
          = 0 := by
        rw [hyw]
        exact indexfRefl hwf
      omega
    · have h := nextEqRtransRSpine L hL hta hgn hunL hm (j + 1) hf rfl hw
        (n := 1) (by omega)
      simp only [Function.iterate_one] at h
      exact h

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.ltFromYSpine
#print axioms Kepler.Text.TameSpine.memFromYSpine
#print axioms Kepler.Text.TameSpine.indexfYtransLeDConstSpine
#print axioms Kepler.Text.TameSpine.nextEqRtransRSpine
#print axioms Kepler.Text.TameSpine.nextYtransConstSpine
