/-
  Kepler.Text.TameSpine.Reduction3Pbflhet2 — tame-corr nb4：nc4 收口五件 +
  nc5 槽版（ztrans_suc_in_ztan_w，PWSSRAT 主件显式槽）。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ §1 nc4 收口三件（工单 1）：
  │  · `indexfYtransEqLmSpine`（HOL Pplhulj.indexf_ytrans_eq_l_m 塔层
  │    face-index 形；V0 = `indexfYtransEqLm` ZIndexf:136 查重命中零重落）
  │    ——lt_indexf 的锚件。
  │  · `ltIndexfInRtransSucNotRtrans`（PBFLHET.hl:250）：eq_indexf（nb3）
  │    + 本件锚 + indexfYtransEqLm1Spine（nb3）+ qcdvkeaTowerSpine（续828）
  │    + indexf_in（nb3）链式 omega。
  │  · `ltFromZSpine`（PBFLHET.hl:347）：indexfTwoPoint（nb3）@d₁:=l'y(0)
  │    + lt_indexf（本笔）+ propertiesOfYtrans0Spine（nb3）@i/@SUC i +
  │    indexf_betwn_eq/indexf_add_* 算术（f 上 y0 ≤ y_i < d < z_i）。
  │ §1' nc4 配套两件（工单 1 的 INDUCT_MEM / ztran_suc_in_rtrans）：
  │  · `inductMemMainResultSpine`（PBFLHET.hl:374）：反证 + ltFromZSpine。
  │  · `ztranSucInRtransSpine`（PBFLHET.hl:392）：propertiesOfYtrans0
  │    @SUC i（供 y0 ∈ r₂）+ memZtransRtrans@SUC i + indexf_refl + 本笔
  │    INDUCT_MEM（d := l'z(i+1)）。
  │ §2 nc5（工单 3）：`ztransSucInZtanWSpine`（PBFLHET.hl:462-511）
  │    **PWSSRAT 主件槽版**（hPw 显式前提，照 J4
  │    `oldnewVertexDisjointOfObdatyb` 先例；aq13 在飞 PWSSRAT spine 形，
  │    落库后一行代入）：ztranSucInRtrans（本笔）+ PWSSRAT ⟸ 半 +
  │    qcdvkeaTowerSpine + indexfConstLeIndexfYtransSpine（nb3）+
  │    indexf_add_left×3 + PPLHULJ@i/@i+1 面链 + omega 反证。
  │    证体相对 HOL 的简化记档：HOL 的三重 DICH 位置二分在 Lean 侧被
  │    indexfConstLe 双实例转移（w 锚 f↔r₁）+ 方程化 omega 取代
  │    （w→z' r₁-index = w→z' f-index 与面链 w→y < w→z ≤ w→y' < w→z'
  │    相抵于 w→y' ≤ w→y）。
  └────────────────────────────────────────────────────────────────

  ┌─ 冻结件（陈述 + 消费树 + 估行 + 卡点）────────────────────────
  │ ① `w_betwn_ztrans_ytran0`（PBFLHET.hl:567-630，64 HOL 行）：
  │   陈述（塔层 i，全在 r₁ 上）：indexf (l'z(i)) w r₁ ≤ indexf (l'z(i))
  │   (l'y(0)) r₁ ∧ indexf (l'z(i)) (l'y(0)) r₁ ≤ indexf (l'z(i)) (l'y(i)) r₁。
  │   已备消费件：propertiesOfYtrans0Spine / nextMarkCaseMemSpine /
  │   indexfConstLeIndexfYtransSpine（均 nb3）+ ytransMemRtrans +
  │   hqymrtx3List + TameList3 全族——**零外部缺口**。
  │   卡点：两合取都需 **l'y(0) 在 r₁ 上的环弧序**（z→w→l'y(0)→l'y(i)，
  │   即排除 y0 ∈ betwn r₁ z w 与 y0 ∈ betwn r₁ y z 之外的余弧）；实测
  │   conj2（y0≤y）**不能**由 propertiesOfYtrans0 conj1/3 的 f 侧事实经
  │   indexfConstLe 免费转移（锚是 l'z 不是 w，indexfConstLe 的界是
  │   conj2 本身——循环）。HOL 原证以 DICH_TAC(17-14)/(20-17)/(36-19)
  │   三层二分 + ARITH 收口，其方程闭包依赖该弧序事实隐式成立。
  │   估行（含弧序引理 port）：80–140。
  │   消费面：INDUCT_LE_MAIN_RESULT（nc6 首件）+ betwn_ztran_ytrans_
  │   suc_const（J4 关键路径）——**nc6 由本件门控**。
  │ ② OHCGKFU 主件 V0 移植（OHCGKFU.hl:162-280，107 HOL 行）：
  │   陈述（i=0 spine 形）：MEM d r ∧ MEM d (rtrans 1) ⇒ indexf (l'z) d r
  │   = indexf (l'z) d (rtrans 1)。V0 重查零命中（aq10_/aqs_ 前缀 + 结论
  │   形双路 grep）。**完整移植方案已勘定**（本轮回滚，见 DELIVERY §2）：
  │   final 二分 → rtransCat 展开 → 窗口支反证（indexfYtransSucLp +
  │   fListPowYtransNotMem + indexf_betwn_eq + indexf_n + markedLemmaYzInFace
  │   全在库，零新增几何）→ 非窗口支 head 锚 indexf 折叠私件两枚 +
  │   d = l'z / betwn r l'z l'y（indexlBetwn+sizeBetwn）/ d = l'y 三支
  │   位置账（betwnCases+antisym 互斥 omega）。估行 150–250。
  │   消费面：trans_indexf_suc（PBFLHET:536，估 35–60，双实例薄组合）→
  │   CASES2 / betwn_ztran_ytrans_suc_const / INDUCT_*。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ qcdvkeaTowerSpine / indexfYtransEqLm1Spine / indexfConstLeIndexfYtransSpine
  │ / indexfInRtransSucNotRtrans / eqIndexfInRtransSucNotRtrans /
  │ indexfTwoPointInRtransSucNotRtrans / propertiesOfYtrans0Spine /
  │ ytransMemRtrans / memZtransRtransSpine / TameList3 indexf-betwn 族）
  │ 同世界零混合；零 Dart 载体件。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Pbflhet1
import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans2
import Kepler.Text.TameSpine.Reduction3QcdvkeaTower
import Kepler.Text.TameSpine.Reduction3NcvibwuTower
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.TameSpine.JcajyduAqZIndexf
import Kepler.Text.TameSpine.JcajyduAqTowerBase
import Kepler.Text.TameSpine.JcajyduAqSnd

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face findFaceDarts_nodup
  findFaceDarts_congr_of_mem mem_darts_of_mem_findFace nextEl_mem_of_mem)

/-! ## §1 nc4 收口 -/

/-- **HOL `Pplhulj.indexf_ytrans_eq_l_m`**（PPLHULJ.hl:114）塔层 i 形
（face-index）：`¬final@i ∧ next_el f x = w ⇒
indexf w (l'y(i)) f = l'm (rtrans i) x`。V0 = `indexfYtransEqLm`
（ZIndexf:136，查重命中零重落）塔层薄包装。 -/
theorem indexfYtransEqLmSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf w (ytransSpine L N r x i) f = lMSpine L (rtransSpine L N r x i) x := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have h := indexfYtransEqLm L hL hgn hunL hmr hf
  rw [hfind, hw] at h
  exact h

/-- **HOL `Pbflhet.lt_indexf_in_rtrans_suc_not_rtrans`**（PBFLHET.hl:250）
塔层 i 形：`d ∈ rtrans(i+1) ∧ d ∉ rtrans(i) ⇒
indexf w d (rtrans(i+1)) < indexf w (l'y(i+1)) (rtrans(i+1))`。
证 = eq_indexf（nb3：w→d 的 r₂-index = f-index）+ indexfYtransEqLmSpine
（l'y(i+1) 的 f-index = l'm）+ indexfYtransEqLm1Spine（nb3：l'y(i+1) 的
r₂-index = l'm）+ qcdvkeaTowerSpine（w→l'z(i) ≤ w→l'y(i+1)，f 上）+
indexf_in（nb3：w→d < w→l'z(i)，f 上）——链式 omega。 -/
theorem ltIndexfInRtransSucNotRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hd0 : d ∉ rtransSpine L N r x i) :
    indexf w d (rtransSpine L N r x (i + 1))
      < indexf w (ytransSpine L N r x (i + 1)) (rtransSpine L N r x (i + 1)) := by
  have heq := eqIndexfInRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw hd1 hd0
  have hin := indexfInRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw hd1 hd0
  have hq := qcdvkeaTowerSpine L hL hta hgn hm i hf hfind hw
  -- 锚等式：l'y(i+1) 的 f-index = r₂-index = l'm
  have hyf := indexfYtransEqLmSpine L hL hta hgn hunL hm (i + 1) hf hfind hw
  have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
  have hw1 : nextEl (rtransSpine L N r x (i + 1)) x = w := by
    rw [hmr1.1.2.2.2.2.2.1, ← hw, ← hfind]
    rfl
  have hyr := indexfYtransEqLm1Spine L hL hta hgn hm (i + 1) hf hw1
  rw [← heq]
  omega

/-- **HOL `Pbflhet.lt_from_z_indexf_in_rtrans_suc_not_rtrans`**
（PBFLHET.hl:347）塔层 i 形：`d ∈ rtrans(i+1) ∧ d ∉ rtrans(i) ⇒
indexf (l'z(i+1)) (l'y(0)) r₂ < indexf (l'z(i+1)) d r₂`。
证 = indexfTwoPoint（nb3）@d₁ := l'y(0)：两前件
`w→l'y(0) < w→d < w→l'y(i+1)`（均在 r₂ 上）——B = lt_indexf（本笔）；
A = propertiesOfYtrans0Spine@i（f 上 w→l'y(0) < w→l'z(i)）+ in_rtrans
（d ∈ betwn f l'y(i) l'z(i) ⟹ l'y(i) < d < l'z(i)）链收口。 -/
theorem ltFromZSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hd0 : d ∉ rtransSpine L N r x i) :
    indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1))
      < indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1)) := by
  have hfi := finalListInductSpine L N r x i hf
  have hmr := aqiunpp3 L hL i hta hgn hm
  obtain ⟨hyf0, hzf0, hlt0⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  rw [hfind] at hyf0 hzf0 hlt0
  rw [hw] at hlt0
  -- propertiesOfYtrans0Spine@SUC i（y0 ∈ r₂、f=r₂ index）与 @i（f 上 y0 ≤ y_i）
  have hprops := propertiesOfYtrans0Spine L hL hta hgn hunL hm (i + 1) hfind hw hf
  have hpropsi := propertiesOfYtrans0Spine L hL hta hgn hunL hm i hfind hw hfi
  have hy0r2 : ytransSpine L N r x 0 ∈ rtransSpine L N r x (i + 1) := hprops.2.2.2
  have hy0eq : indexf w (ytransSpine L N r x 0) f
      = indexf w (ytransSpine L N r x 0) (rtransSpine L N r x (i + 1)) := hprops.1
  have hle0 : indexf w (ytransSpine L N r x 0) f
      ≤ indexf w (ytransSpine L N r x i) f := hpropsi.2.2.1
  -- f 上：w→y_i < w→d（d ∈ betwn f y_i z_i）
  have hbet := inRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw hd1 hd0
  rw [show ytransSpine L N r x i = lYSpine L (rtransSpine L N r x i) x from rfl,
      show ztransSpine L N r x i
        = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl] at hbet
  rw [show ytransSpine L N r x i = lYSpine L (rtransSpine L N r x i) x from rfl] at hle0
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hne := hqymrtx3List L hL hgn hunL hmr hfi
  obtain ⟨hp1, hp2⟩ := (indexfBetwnEq hne hfnd hyf0 hzf0).mp hbet
  have hE1 := indexfAddLeft hwf hyf0 hzf0 (Nat.le_of_lt hlt0)
  have hE2 := indexfAddBetwn hne hfnd hyf0 hbet hzf0
  have hdf : d ∈ f := betwnMem hbet
  have hdzle : indexf d (lZSpine L (ntransSpine L N r x i)
      (rtransSpine L N r x i) x) f
      ≤ indexf w (lZSpine L (ntransSpine L N r x i)
        (rtransSpine L N r x i) x) f := by omega
  have hE3 := indexfAddRight hwf hdf hzf0 hdzle
  -- A：indexf w y0 r₂ < indexf w d r₂
  have heq := eqIndexfInRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw hd1 hd0
  have hA : indexf w (ytransSpine L N r x 0) (rtransSpine L N r x (i + 1))
      < indexf w d (rtransSpine L N r x (i + 1)) := by
    rw [← hy0eq, ← heq]
    omega
  -- B：indexf w d r₂ < indexf w l'y(i+1) r₂
  have hB := ltIndexfInRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw hd1 hd0
  -- indexfTwoPoint @i := SUC i, d₁ := l'y(0)
  exact indexfTwoPointInRtransSucNotRtrans L hL hta hgn hunL hm (i + 1) hf
    hfind hw hd1 hy0r2 hB hA

/-- **HOL `Pbflhet.INDUCT_MEM_MAIN_RESULT`**（PBFLHET.hl:374）塔层 i 形：
`indexf (l'z(i+1)) d r₂ ≤ indexf (l'z(i+1)) (l'y(0)) r₂ ⇒ MEM d r₁`。
证 = 反证（d ∉ r₁）+ ltFromZSpine 与前提相抵。 -/
theorem inductMemMainResultSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hle : indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1))) :
    d ∈ rtransSpine L N r x i := by
  by_cases hd0 : d ∈ rtransSpine L N r x i
  · exact hd0
  · exact absurd (ltFromZSpine L hL hta hgn hunL hm i hf hfind hw hd1 hd0)
      (by omega)

/-- **HOL `Pbflhet.ztran_suc_in_rtrans`**（PBFLHET.hl:392）塔层 i 形：
`¬final(i+1) ⇒ MEM (l'z(i+1)) r₁`。
证 = propertiesOfYtrans0Spine@SUC i（供 y0 ∈ r₂）+ memZtransRtrans@SUC i
（z₁ ∈ r₂）+ indexf_refl（z₁→z₁ = 0 ≤ 界）+ 本笔 INDUCT_MEM
（d := l'z(i+1)）。 -/
theorem ztranSucInRtransSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x i := by
  have hz1 : ztransSpine L N r x (i + 1)
      ∈ rtransSpine L N r x (i + 1) :=
    memZtransRtransSpine L hL hgn hunL hta hm (i + 1) hf
  refine inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hz1 ?_
  rw [indexfRefl hz1]
  exact Nat.zero_le _

/-! ## §2 nc5：ztrans_suc_in_ztan_w（PWSSRAT 主件槽版） -/

/-- **HOL `Pbflhet.ztrans_suc_in_ztran_w`**（PBFLHET.hl:462-511）塔层 i 形，
**PWSSRAT 主件槽版**（hPw：aq13 在飞 PWSSRAT spine 主件，落库后一行代入）：
`¬final(i+1) ⇒ indexf (l'z(i)) (l'z(i+1)) r₁ < indexf (l'z(i)) w r₁`。
证（与 HOL 同构，二分）：lt 支直接收口；≤ 支反证——
indexf_add_left×3（z,w,z₁ / z,z₁,y / z,w,y）+ indexfConstLeIndexfYtransSpine
双实例（z₁/y 的 w 锚 f↔r₁ 转移，界由 d ≤ e 供）+ QCDVKEA 塔层形 +
PPLHULJ@i/@i+1 面链（w→y < w→z ≤ w→y' < w→z' 与 w→z' r₁ = w→z' f ≤ w→y r₁
= w→y f 相抵）。 -/
theorem ztransSucInZtanWSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hPw : ∀ {N' : List (List (ℕ × ℕ))} {r' : List (ℕ × ℕ)},
      MarkedListSpineFull hL N' r' x → ¬ finalListSpine L r' →
      ∀ d' ∈ r',
        (d' ∈ rtransSpine L N' r' x 1
          ↔ indexf (lZSpine L N' r' x) d' r'
            ≤ indexf (lZSpine L N' r' x) (lYSpine L r' x) r')) :
    indexf (ztransSpine L N r x i) (ztransSpine L N r x (i + 1))
        (rtransSpine L N r x i)
      < indexf (ztransSpine L N r x i) w (rtransSpine L N r x i) := by
  have hfi := finalListInductSpine L N r x i hf
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
  -- l'z(i+1) ∈ r₁（本笔 ztranSucInRtransSpine）
  have hz1r1 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x i :=
    ztranSucInRtransSpine L hL hta hgn hunL hm i hf hfind hw
  -- PWSSRAT ⟸ 半：l'z(i+1) ∈ r₂ ⟹ indexf z z₁ r₁ ≤ indexf z y r₁
  have hz1r2 : ztransSpine L N r x (i + 1)
      ∈ rtransSpine L N r x (i + 1) :=
    memZtransRtransSpine L hL hgn hunL hta hm (i + 1) hf
  have hPle : indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
        (ztransSpine L N r x (i + 1)) (rtransSpine L N r x i)
      ≤ indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
        (lYSpine L (rtransSpine L N r x i) x) (rtransSpine L N r x i) :=
    (hPw hmr hfi (ztransSpine L N r x (i + 1)) hz1r1).mp
      (by rw [← rtransSuccSpine L N r x i]; exact hz1r2)
  -- 面表（PPLHULJ@i / @i+1）与 QCDVKEA
  obtain ⟨hyf0, hzf0, hlt0⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  rw [hfind, hw] at hlt0
  obtain ⟨hyf1, hzf1, hlt1⟩ := pplhuljV0 L hL hgn hunL hmr1 hf
  rw [hfind, hw] at hlt1
  have hq := qcdvkeaTowerSpine L hL hta hgn hm i hf hfind hw
  -- 统一拼写（z 锚归 lZSpine(i)）
  rw [show ztransSpine L N r x i
      = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl]
  -- 二分
  by_cases hlt : indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
        (ztransSpine L N r x (i + 1)) (rtransSpine L N r x i)
      < indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x) w
        (rtransSpine L N r x i)
  · exact hlt
  · exfalso
    have hle1 : indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x) w
          (rtransSpine L N r x i)
        ≤ indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
          (ztransSpine L N r x (i + 1)) (rtransSpine L N r x i) := by omega
    have hzr1 : lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
        ∈ rtransSpine L N r x i := memZtransRtransSpine L hL hgn hunL hta hm i hfi
    have hwr1 : w ∈ rtransSpine L N r x i := by
      have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
      rw [← hw']
      exact aq10_nextMarkMemRTrans L hL hgn hmr
    have hyr1 : lYSpine L (rtransSpine L N r x i) x ∈ rtransSpine L N r x i :=
      ytransMemRtrans L hL hgn hmr hfi
    -- z 锚三方程
    have hE1 := indexfAddLeft hzr1 hwr1 hz1r1 hle1
    have hE2 := indexfAddLeft hzr1 hz1r1 hyr1 hPle
    have hE3 := indexfAddLeft hzr1 hwr1 hyr1 (by omega)
    -- d ≤ e：indexf w z₁ r₁ ≤ indexf w y r₁
    have hdle : indexf w (ztransSpine L N r x (i + 1)) (rtransSpine L N r x i)
        ≤ indexf w (lYSpine L (rtransSpine L N r x i) x) (rtransSpine L N r x i) := by
      omega
    -- constLe 双实例转移（w 锚 f↔r₁）
    have hc1 := indexfConstLeIndexfYtransSpine L hL hta hgn hm i hfi hfind hw
      hz1r1 hdle
    have hc2 := indexfConstLeIndexfYtransSpine L hL hta hgn hm i hfi hfind hw
      hyr1 (le_refl _)
    rw [show indexf w (lYSpine L (rtransSpine L N r x i) x) (rtransSpine L N r x i)
        = indexf w (lYSpine L (rtransSpine L N r x i) x) f from hc2] at hdle
    rw [show indexf w (ztransSpine L N r x (i + 1)) (rtransSpine L N r x i)
        = indexf w (ztransSpine L N r x (i + 1)) f from hc1] at hdle
    rw [(show ztransSpine L N r x (i + 1)
        = lZSpine L (ntransSpine L N r x (i + 1)) (rtransSpine L N r x (i + 1)) x
          from rfl).symm] at hlt1
    rw [show ztransSpine L N r x i
        = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl,
      show ytransSpine L N r x (i + 1)
        = lYSpine L (rtransSpine L N r x (i + 1)) x from rfl] at hq
    omega
end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.indexfYtransEqLmSpine
#print axioms Kepler.Text.TameSpine.ltIndexfInRtransSucNotRtrans
#print axioms Kepler.Text.TameSpine.ltFromZSpine
#print axioms Kepler.Text.TameSpine.inductMemMainResultSpine
#print axioms Kepler.Text.TameSpine.ztranSucInRtransSpine
#print axioms Kepler.Text.TameSpine.ztransSucInZtanWSpine
