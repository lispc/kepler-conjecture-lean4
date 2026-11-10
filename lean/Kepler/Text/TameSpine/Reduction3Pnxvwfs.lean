/-
  Kepler.Text.TameSpine.Reduction3Pnxvwfs — tame-corr nb7：PNXVWFS 章
  五件全收口（余量段：J4 链 CASES2 / betwn_ztran_ytrans_suc_const 前端）。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ ① `ytransInSucSpine`（PNXVWFS.hl:32-42 ytrans_in_suc）：
  │    ¬final(i+1) ⇒ MEM (l'y(i+1)) r₁。证 = ytrans_mem_rtrans@(i+1)
  │    + lt_indexf_in_rtrans_suc_not_rtrans（nb4）与 d := l'y(i+1)
  │    自反相抵（HOL ARITH_RULE `~(a<a)`）。
  │ ② `indexfYLeZInRSpine`（PNXVWFS.hl:45-64 indexf_y_le_z_in_r）：
  │    ¬final(i) ⇒ indexf w (l'y(i)) r₁ < indexf w (l'z(i)) r₁。
  │    证 = V0 形查重命中 `aq10_indexfYLeZInR0`（Leaf10，AQ7.hl:181）
  │    塔层 i 直投（w 经 hfind/hw 桥接拼写）。
  │ ③ `ytranSucBetwnZZSucSpine`（PNXVWFS.hl:66-117
  │    ytran_suc_betwn_z_z_suc）：¬final(i+1) ⇒
  │    indexf (l'z(i)) (l'y(i+1)) r₁ < indexf (l'z(i)) (l'z(i+1)) r₁。
  │    证 = OHCGKFU 塔层形双实例（l'y(i+1)/l'z(i+1) 的 r₁↔r₂ 不变）
  │    + QCDVKEA 塔层形（w→z f ≤ w→l'y(i+1) f）+ NCVIBWU 塔层形
  │    @j:=w→z f（w→z r₂ = w→z f，经 indexf_n 折回）+ indexf_y_le_z_in_r
  │    @(i+1) + indexf_add_left×2（HOL 第三条 [w;y₁;z₁;r₂] 在 omega 下
  │    冗余，省）+ omega（z→y₁ = w→y₁ − w→z <
  │    w→z₁ − w→z = z→z₁，r₂ 侧经双 OHCGKFU 回 r₁）。
  │ ④ `pnxvwfs1Spine`（PNXVWFS.hl:120-157 PNXVWFS1）：¬final(i) ⇒
  │    MEM (l'y(i)) r。零支 ytrans_mem_rtrans@0；正支 ① + ③ +
  │    ztrans_suc_in_ztran_w + w_betwn conj1 链式 omega（z→l'y(i) <
  │    z→l'z(i) < z→w ≤ z→l'y(0)）+ PBFLHET @ri:=r_j。
  │ ⑤ `pnxvwfs2Spine`（PNXVWFS.hl:160-176 PNXVWFS2）：¬final(i) ⇒
  │    MEM (l'z(i)) r。证 = mem_ztrans_rtrans@i + indexf_refl +
  │    PBFLHET @d:=l'z(i)（HOL 同构）。
  │ 陈述重述记档：HOL 的 f/w 自由变元在 ③④ 以 `rfl` 桥（f :=
  │ find_face L x、w := next_el f x）内联，与 nb1 消费面约定一致。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ memZtransRtransSpine / ztransInSucSpine / ytransMemRtrans /
  │ finalListInductSpine / aq10_indexfYLeZInR0 / pplhuljV0 /
  │ qcdvkeaTowerSpine / ncvibwuTowerSpine / ohcgkfuTowerSpine /
  │ ztranSucInRtransSpine / ztransSucInZtranWSpineClosed /
  │ wBetwnZtransYtran0Spine / pbflhetSpine / ltIndexfInRtransSucNotRtrans
  │ / indexfConstLeIndexfYtransSpine / indexfN / indexfAddLeft /
  │ aq10_memNextMarkInface / TameLp 面件）同世界零混合；零 Dart 载体件。
  │ 全文件默认心跳、linter 全开（零 set_option 覆盖）。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Pbflhet4

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup)

/-! ## §1 ytrans_in_suc + indexf_y_le_z_in_r（PNXVWFS.hl:32-64） -/

/-- **HOL `Pnxvwfs.ytrans_in_suc`**（PNXVWFS.hl:32-42）塔层 i 形：
`¬final(i+1) ⇒ MEM (l'y(i+1)) r₁`。
证 = ytrans_mem_rtrans@(i+1)（l'y(i+1) ∈ r₂）+ nb4
lt_indexf_in_rtrans_suc_not_rtrans @d:=l'y(i+1) 与自身相抵
（HOL `~(a<a)` 反证）。 -/
theorem ytransInSucSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    ytransSpine L N r x (i + 1) ∈ rtransSpine L N r x i := by
  have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
  have hy1r2 : ytransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
    ytransMemRtrans L hL hgn hmr1 hf
  by_contra hnot
  exact absurd
    (ltIndexfInRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw hy1r2 hnot)
    (lt_irrefl _)

/-- **HOL `Pnxvwfs.indexf_y_le_z_in_r`**（PNXVWFS.hl:45-64）塔层 i 形：
`¬final(i) ⇒ indexf w (l'y(i)) r₁ < indexf w (l'z(i)) r₁`。
V0 形查重命中 `aq10_indexfYLeZInR0`（Leaf10，AQ7.hl:181）塔层 i 直投。 -/
theorem indexfYLeZInRSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf w (ytransSpine L N r x i) (rtransSpine L N r x i)
      < indexf w (ztransSpine L N r x i) (rtransSpine L N r x i) := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have h := aq10_indexfYLeZInR0 L hL hgn hmr hf
  rw [hfind, hw] at h
  exact h

/-! ## §2 ytran_suc_betwn_z_z_suc（PNXVWFS.hl:66-117） -/

/-- **HOL `Pnxvwfs.ytran_suc_betwn_z_z_suc`**（PNXVWFS.hl:66-117）塔层 i 形：
`¬final(i+1) ⇒ indexf (l'z(i)) (l'y(i+1)) r₁ <
indexf (l'z(i)) (l'z(i+1)) r₁`。
证 = OHCGKFU 塔层形双实例（r₁↔r₂ 不变）+ QCDVKEA + NCVIBWU 塔层形
（w→z r₂ = w→z f）+ indexf_y_le_z_in_r@(i+1) + indexf_add_left×2 +
omega。 -/
theorem ytranSucBetwnZZSucSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf (ztransSpine L N r x i) (ytransSpine L N r x (i + 1))
        (rtransSpine L N r x i)
      < indexf (ztransSpine L N r x i) (ztransSpine L N r x (i + 1))
        (rtransSpine L N r x i) := by
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    finalListInductSpine L N r x i hf
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
  have hy1r1 : ytransSpine L N r x (i + 1) ∈ rtransSpine L N r x i :=
    ytransInSucSpine L hL hta hgn hunL hm i hf hfind hw
  have hzr2 : ztransSpine L N r x i ∈ rtransSpine L N r x (i + 1) :=
    ztransInSucSpine L hL hta hgn hm i hfi
  have hy1r2 : ytransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
    ytransMemRtrans L hL hgn hmr1 hf
  have hz1r1 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x i :=
    ztranSucInRtransSpine L hL hta hgn hunL hm i hf hfind hw
  have hz1r2 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
    memZtransRtransSpine L hL hgn hunL hta hm (i + 1) hf
  -- OHCGKFU 双实例：z 锚不动，l'y(i+1)/l'z(i+1) 的 r₁-index = r₂-index
  have hO1 := ohcgkfuTowerSpine L hL hta hgn hunL hm i hy1r1 hy1r2
  have hO2 := ohcgkfuTowerSpine L hL hta hgn hunL hm i hz1r1 hz1r2
  -- QCDVKEA @i：w→z f ≤ w→l'y(i+1) f（f 上）
  have hQ := qcdvkeaTowerSpine L hL hta hgn hm i hf hfind hw
  have hC1 : indexf w (ytransSpine L N r x (i + 1))
        (rtransSpine L N r x (i + 1))
      = indexf w (ytransSpine L N r x (i + 1)) f :=
    indexfConstLeIndexfYtransSpine L hL hta hgn hm (i + 1) hf hfind hw
      hy1r2 (le_refl _)
  -- NCVIBWU 塔层形 @j:=w→z f + indexf_n 折回 z：w→z r₂ = w→z f
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  obtain ⟨-, hzf, -⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  rw [hfind] at hzf
  have hzif : ztransSpine L N r x i ∈ f := hzf
  obtain ⟨-, hidx⟩ := ncvibwuTowerSpine L hL hta hgn hm i hfi hfind hw
    (le_refl (indexf w (ztransSpine L N r x i) f))
  rw [indexfN hwf hzif hfnd] at hidx
  have hY := indexfYLeZInRSpine L hL hta hgn hm (i + 1) hf hfind hw
  have hwr2 : w ∈ rtransSpine L N r x (i + 1) := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm (i + 1)
  -- r₂ 上两方程：w→z + z→y₁ = w→y₁、w→z + z→z₁ = w→z₁
  have hA1 := indexfAddLeft hwr2 hzr2 hy1r2 (by omega)
  have hA3 := indexfAddLeft hwr2 hzr2 hz1r2 (by omega)
  omega

/-! ## §3 PNXVWFS1 / PNXVWFS2（PNXVWFS.hl:120-176） -/

/-- **HOL `Pnxvwfs.PNXVWFS1`**（PNXVWFS.hl:120-157）塔层 i 形：
`¬final(i) ⇒ MEM (l'y(i)) r`。
零支 ytrans_mem_rtrans@0（rtrans 0 ≡ r 定义级）；正支：ytrans_in_suc @j
+ ytran_suc_betwn_z_z_suc @j + ztrans_suc_in_ztran_w + w_betwn conj1
链式 omega（z→l'y(i) < z→l'z(i) < z→w ≤ z→l'y(0)，r_j 上）+
PBFLHET @d:=l'y(i)。 -/
theorem pnxvwfs1Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    ytransSpine L N r x i ∈ r := by
  cases i with
  | zero =>
    rw [show rtransSpine L N r x 0 = r from rfl] at hf
    rw [show ytransSpine L N r x 0 = lYSpine L r x from rfl]
    exact ytransMemRtrans L hL hgn hm hf
  | succ j =>
    have hfj : ¬ finalListSpine L (rtransSpine L N r x j) :=
      finalListInductSpine L N r x j hf
    have hy1rj : ytransSpine L N r x (j + 1) ∈ rtransSpine L N r x j :=
      ytransInSucSpine L hL hta hgn hunL hm j hf rfl rfl
    have hB := ytranSucBetwnZZSucSpine L hL hta hgn hunL hm j hf rfl rfl
    have hZ := ztransSucInZtranWSpineClosed L hL hta hgn hunL hm j hf rfl rfl
    obtain ⟨hW1, -⟩ := wBetwnZtransYtran0Spine L hL hta hgn hunL hm j hfj
      rfl rfl
    exact (pbflhetSpine L hL hta hgn hunL hm j hfj hy1rj (by omega)).1

/-- **HOL `Pnxvwfs.PNXVWFS2`**（PNXVWFS.hl:160-176）塔层 i 形：
`¬final(i) ⇒ MEM (l'z(i)) r`。
证 = mem_ztrans_rtrans@i + indexf_refl + PBFLHET @d:=l'z(i)（HOL 同构）。 -/
theorem pnxvwfs2Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    ztransSpine L N r x i ∈ r := by
  have hz : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hf
  have hle : indexf (ztransSpine L N r x i) (ztransSpine L N r x i)
        (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
        (rtransSpine L N r x i) := by
    rw [indexfRefl hz]
    exact Nat.zero_le _
  exact (pbflhetSpine L hL hta hgn hunL hm i hf hz hle).1

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.ytransInSucSpine
#print axioms Kepler.Text.TameSpine.indexfYLeZInRSpine
#print axioms Kepler.Text.TameSpine.ytranSucBetwnZZSucSpine
#print axioms Kepler.Text.TameSpine.pnxvwfs1Spine
#print axioms Kepler.Text.TameSpine.pnxvwfs2Spine
