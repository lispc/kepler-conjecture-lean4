/-
  Kepler.Text.TameSpine.Reduction3Pbflhet4 — tame-corr nb7：nc6 全链收口
  （w_betwn 解冻 + INDUCT 五件 + PBFLHET_ALL + PBFLHET，全部无条件形）。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ ① `wBetwnZtransYtran0Spine`（PBFLHET.hl:567-626，64 HOL 行）——
  │   **解冻**（nb4/nb5/nb6 三轮冻结勘误）：HOL 原证支 2（w ∈ betwn
  │   r₁ z y）根本不对 y0 做位置二分，而是 indexf_add_right[z;y0;y;r1]，
  │   其界 indexf y0 y r₁ ≤ indexf z y r₁ 由 indexf_add_left[w;y0;y;r1]
  │   （E）与 indexf_add_betwn[z;w;y;r1]（F）两方程算术导出；前任改走
  │   betwnCases 四支切分是偏离原证的自造卡点，零位置引理需求。
  │ ② `inductLeMainResultSpine`（PBFLHET.hl:631-674 INDUCT_LE_MAIN_RESULT，
  │   44 HOL 行）：case 二分（indexf z d r₁ ≤ indexf z y₀ r₁ ∨ >）——
  │   ≤ 支即目标；> 支：trans_indexf_suc 双实例（(z₁,y₀) 界由
  │   ztrans_suc_in_ztran_w + w_betwn conj1 导出、(z₁,d) 界再由 > 支导出）
  │   + indexf_add_left×2 + omega（indexf z d r₁ = z z₁ + z₁ d r₁ =
  │   z z₁ + z₁ d r₂ ≤ z z₁ + z₁ y₀ r₂ = z z₁ + z₁ y₀ r₁ = indexf z y₀ r₁）。
  │ ③ `inductConstMainResultSpine`（PBFLHET.hl:678-719，42 HOL 行）：
  │   ②的 LE + trans_indexf_suc 双实例（(d,y₀) 界 = LE、(z₁,y₀) 界 =
  │   ztrans_suc_in_ztran_w + w_betwn conj1）+ indexf_add_left r₂ +
  │   indexf_add_right r₁ + omega（z₁ d r₁ = z₁ y₀ r₁ − d y₀ r₁ =
  │   z₁ y₀ r₂ − d y₀ r₂ = z₁ d r₂）。
  │ ④ `inductMainResultSpine`（PBFLHET.hl:722-743）：② ③ INDUCT_MEM
  │   （nb4）三件直拼（HOL THENL 三支）。
  │ ⑤ `inductConstMainResultTwoSpine`（PBFLHET.hl:749-789）：INDUCT_CONST
  │   双实例（d / d1）+ indexf_add_left r₂（界 = 前提 hle1）+
  │   INDUCT_MEM 双实例 + indexf_add_left r₁（界由 ③ 双实例 omega）。
  │ ⑥ `inductLeMainResultTwoSpine`（PBFLHET.hl:793-844）：INDUCT_LE
  │   双实例 + indexf_add_left r₁/r₂ 四方程 + trans_indexf_suc 双实例 +
  │   omega（d y₀ ≤ d1 y₀ ⟹ z d1 r₁ ≤ z d r₁）。
  │ ⑦ `inductMainResultTwoSpine`（PBFLHET.hl:849-882）：⑥ ⑤ INDUCT_MEM
  │   双实例五合取直拼。
  │ ⑧ `pbflhetAllSpine`（PBFLHET.hl:888-923 PBFLHET_ALL）：对 m := i−t
  │   归纳（即 HOL INDUCT_REV 翻转；照 finalListInduct1Spine 的差值归纳
  │   约定）+ FINAL_LIST_INDUCT1（¬final 下传）+ ⑦ @j:=i−SUC t。
  │ ⑨ `pbflhetSpine`（PBFLHET.hl:928-948 PBFLHET）：⑧ @t:=0、d1 := l'z(i)
  │   （mem_ztrans_rtrans@i + indexf_refl 供第二前提）+ rtrans 0 ≡ r
  │   定义级。结论 `MEM d r ∧ indexf l'z(i) d ri = indexf l'z(i) d r`。
  │ 陈述重述记档：HOL 的 ri/w 自由变元及等式前提（rtrans i = ri、
  │ next_el (find_face x) x = w）在 ⑧⑨ 按 ri 内联、w 省去（结论不含
  │ w，等价重述；照 nb1 nextMarkMemRTransSpine 前提子集先例）。
  │ **零 hWb 槽**：① 已解冻，nc6 全线无条件落（工单的 hWb 槽口径以
  │ 「槽对应真实上游缺口」为前提，本笔缺口已不存在）。
  └────────────────────────────────────────────────────────────────

  ┌─ 勘误记档（对 nb4/nb5/nb6 冻结诊断）───────────────────────────
  │ 1. w_betwn「几何卡点」（l'y(0) loop 位置不在 z→w 段 / HQYMRTX 位置
  │    引理需求）不成立：HOL 原证 PBFLHET.hl:610-626 支 2 无位置二分，
  │    y0 的弧序由 indexf_add_right 的界方程隐式承载。
  │ 2. INDUCT_LE「whnf 死磨」（sInf 不可归约 / import 集差异）不成立：
  │    nb6 二分探针 ProbeB 的 hz1r2 ascription 把 lZSpine 实参下标写成
  │    i（证明项在 i+1），是**类型错位**——错位两侧的 defeq 判否需沿
  │    iterate/transformListSpine/lPSpine/sInf 全展开，任何心跳预算下
  │    都表现为 whnf 超时（本轮 P1/P2/P3 探针机器证据）；正确下标的
  │    ascription 默认心跳即过（P1 5 秒）。本世界操作纪律：whnf 超时
  │    首查类型错位，不加大心跳预算。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ memZtransRtransSpine / nextMarkMemRTransSpine / ytransMemRtrans /
  │ finalListInductSpine / finalListInduct1Spine / inductMemMainResultSpine
  │ / ztranSucInRtransSpine / ztransSucInZtranWSpineClosed /
  │ transIndexfSucSpine / propertiesOfYtrans0Spine /
  │ indexfConstLeIndexfYtransSpine / nextMarkCaseMemSpine / hqymrtx3List
  │ / normalListUniqNonnil / TameList3 indexf 族）同世界零混合；
  │ 零 Dart 载体件。全文件默认心跳、linter 全开（零 set_option 覆盖，
  │ autoImplicit false 除外）。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Pbflhet3
import Kepler.Text.TameSpine.Reduction3Pbflhet2
import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans
import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans2
import Kepler.Text.TameSpine.JcajyduAqTowerBase

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl)

/-! ## §1 w_betwn_ztrans_ytran0（PBFLHET.hl:567-626）——解冻 -/

/-- **HOL `Pbflhet.w_betwn_ztrans_ytran0`**（PBFLHET.hl:567-626）塔层 i 形
（无条件形，全在 r₁ 上）：`indexf (l'z(i)) w r₁ ≤ indexf (l'z(i)) (l'y(0)) r₁
∧ indexf (l'z(i)) (l'y(0)) r₁ ≤ indexf (l'z(i)) (l'y(i)) r₁`。
证（与 HOL 同构，支 2 无位置二分）：DICH 桥（indexf_const_le_indexf_ytrans
@y + properties_of_ytrans0 (1)(3) 算术）+ indexf_add_left[w;y0;y;r1]（E）；
w = y 支：E 零和 + indexf_zero ⟹ y0 = y 两合取自反；w ∈ betwn r₁ z y 支：
indexf_add_betwn[z;w;y;r1]（F）+ 界（y0→y ≤ z→y，由 E/F 算术）+
indexf_add_right[z;y0;y;r1]（H）+ omega（z→w + w→y0 = z→y0 ≤ z→y）。 -/
theorem wBetwnZtransYtran0Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf (ztransSpine L N r x i) w (rtransSpine L N r x i)
        ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
          (rtransSpine L N r x i)
      ∧ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
          (rtransSpine L N r x i)
        ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x i)
          (rtransSpine L N r x i) := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hz : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hf
  obtain ⟨hP1, -, hP3, hy0⟩ :=
    propertiesOfYtrans0Spine L hL hta hgn hunL hm i hfind hw hf
  have hy : ytransSpine L N r x i ∈ rtransSpine L N r x i :=
    ytransMemRtrans L hL hgn hmr hf
  -- indexf_const_le_indexf_ytrans @y（自反界）：w→y r₁ = w→y f
  have hC : indexf w (ytransSpine L N r x i) (rtransSpine L N r x i)
      = indexf w (ytransSpine L N r x i) f :=
    indexfConstLeIndexfYtransSpine L hL hta hgn hm i hf hfind hw hy (le_refl _)
  -- DICH 桥：w→y0 r₁ ≤ w→y r₁（props (1)+(3) 与 hC 算术）
  have hD : indexf w (ytransSpine L N r x 0) (rtransSpine L N r x i)
      ≤ indexf w (ytransSpine L N r x i) (rtransSpine L N r x i) := by omega
  have hwr : w ∈ rtransSpine L N r x i := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm i
  -- E：indexf_add_left[w;y0;y;r1]
  have hE := indexfAddLeft hwr hy0 hy hD
  rcases nextMarkCaseMemSpine L hL hta hgn hm i hf hfind hw with heq | hbet
  · -- 支 1：w = y ⟹ E 零和 ⟹ y0 = y
    rw [heq, indexfRefl hy] at hE
    have h0 : indexf (ytransSpine L N r x i) (ytransSpine L N r x 0)
        (rtransSpine L N r x i) = 0 := by omega
    have hyy0 : ytransSpine L N r x i = ytransSpine L N r x 0 :=
      indexfZeroEq hy hy0 h0
    rw [heq, hyy0]
    exact ⟨le_refl _, le_refl _⟩
  · -- 支 2：w ∈ betwn r₁ z y ⟹ F + 界 + H（indexf_add_right），零位置二分
    have hne : ztransSpine L N r x i ≠ ytransSpine L N r x i :=
      Ne.symm (hqymrtx3List L hL hgn hunL hmr hf)
    have hrnd : (rtransSpine L N r x i).Nodup :=
      (normalListUniqNonnil hmr.1.2.1 hmr.1.2.2.1).1
    have hF := indexfAddBetwn hne hrnd hz hbet hy
    have hG : indexf (ytransSpine L N r x 0) (ytransSpine L N r x i)
          (rtransSpine L N r x i)
        ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x i)
          (rtransSpine L N r x i) := by omega
    have hH := indexfAddRight hz hy0 hy hG
    constructor <;> omega

/-! ## §2 INDUCT_LE_MAIN_RESULT（PBFLHET.hl:631-674） -/

/-- **HOL `Pbflhet.INDUCT_LE_MAIN_RESULT`**（PBFLHET.hl:631-674）塔层 i 形：
`¬final(i+1) ∧ d ∈ r₂ ∧ indexf (l'z(i+1)) d r₂ ≤ indexf (l'z(i+1)) (l'y(0)) r₂
⇒ indexf (l'z(i)) d r₁ ≤ indexf (l'z(i)) (l'y(0)) r₁`。
证（二分）：≤ 支即目标；> 支：trans_indexf_suc 双实例（(z₁,y₀) 界由
ztrans_suc_in_ztran_w + w_betwn conj1、(z₁,d) 界再由 > 支）+
indexf_add_left×2 + omega 反证。 -/
theorem inductLeMainResultSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd2 : d ∈ rtransSpine L N r x (i + 1))
    (hle : indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1))) :
    indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
        (rtransSpine L N r x i) := by
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    finalListInductSpine L N r x i hf
  have hz1r1 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x i :=
    ztranSucInRtransSpine L hL hta hgn hunL hm i hf hfind hw
  have hzr1 : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hfi
  have hz1r2 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
    memZtransRtransSpine L hL hgn hunL hta hm (i + 1) hf
  obtain ⟨hW1, -⟩ := wBetwnZtransYtran0Spine L hL hta hgn hunL hm i hfi hfind hw
  have hZ := ztransSucInZtranWSpineClosed L hL hta hgn hunL hm i hf hfind hw
  have hd1 : d ∈ rtransSpine L N r x i :=
    inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd2 hle
  have hy0r1 : ytransSpine L N r x 0 ∈ rtransSpine L N r x i :=
    (propertiesOfYtrans0Spine L hL hta hgn hunL hm i hfind hw hfi).2.2.2
  have hy0r2 : ytransSpine L N r x 0 ∈ rtransSpine L N r x (i + 1) :=
    (propertiesOfYtrans0Spine L hL hta hgn hunL hm (i + 1) hfind hw hf).2.2.2
  by_contra hcon
  -- trans (z₁, y₀)：界 = z₁ < w ≤ y₀（r₁ 上）
  have hzy0 : indexf (ztransSpine L N r x i) (ztransSpine L N r x (i + 1))
        (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
        (rtransSpine L N r x i) := by omega
  have hT1 := transIndexfSucSpine L hL hta hgn hunL hm i hfi hy0r1 hz1r1
    hy0r2 hz1r2 hzy0
  -- trans (z₁, d)：界 = z₁ ≤ y₀ < d（r₁ 上，> 支）
  have hzd : indexf (ztransSpine L N r x i) (ztransSpine L N r x (i + 1))
        (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) d (rtransSpine L N r x i) := by omega
  have hT2 := transIndexfSucSpine L hL hta hgn hunL hm i hfi hd1 hz1r1
    hd2 hz1r2 hzd
  have hA1 := indexfAddLeft hzr1 hz1r1 hy0r1 hzy0
  have hA2 := indexfAddLeft hzr1 hz1r1 hd1 hzd
  omega

/-! ## §3 INDUCT_CONST_MAIN_RESULT（PBFLHET.hl:678-719） -/

/-- **HOL `Pbflhet.INDUCT_CONST_MAIN_RESULT`**（PBFLHET.hl:678-719）塔层 i 形：
`¬final(i+1) ∧ d ∈ r₂ ∧ indexf (l'z(i+1)) d r₂ ≤ indexf (l'z(i+1)) (l'y(0)) r₂
⇒ indexf (l'z(i+1)) d r₁ = indexf (l'z(i+1)) d r₂`。
证 = INDUCT_LE + trans_indexf_suc 双实例（(d,y₀) 界 = LE、(z₁,y₀) 界 =
ztrans_suc_in_ztran_w + w_betwn conj1）+ indexf_add_left r₂ +
indexf_add_right r₁ + omega。 -/
theorem inductConstMainResultSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd2 : d ∈ rtransSpine L N r x (i + 1))
    (hle : indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1))) :
    indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x i)
      = indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1)) := by
  have hLE := inductLeMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd2 hle
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    finalListInductSpine L N r x i hf
  have hd1 : d ∈ rtransSpine L N r x i :=
    inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd2 hle
  have hy0r1 : ytransSpine L N r x 0 ∈ rtransSpine L N r x i :=
    (propertiesOfYtrans0Spine L hL hta hgn hunL hm i hfind hw hfi).2.2.2
  have hy0r2 : ytransSpine L N r x 0 ∈ rtransSpine L N r x (i + 1) :=
    (propertiesOfYtrans0Spine L hL hta hgn hunL hm (i + 1) hfind hw hf).2.2.2
  -- trans (d, y₀)：界 = LE（r₁ 上）
  have hT1 := transIndexfSucSpine L hL hta hgn hunL hm i hfi hy0r1 hd1
    hy0r2 hd2 hLE
  obtain ⟨hW1, -⟩ := wBetwnZtransYtran0Spine L hL hta hgn hunL hm i hfi hfind hw
  have hZ := ztransSucInZtranWSpineClosed L hL hta hgn hunL hm i hf hfind hw
  have hzy0 : indexf (ztransSpine L N r x i) (ztransSpine L N r x (i + 1))
        (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
        (rtransSpine L N r x i) := by omega
  have hz1r1 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x i :=
    ztranSucInRtransSpine L hL hta hgn hunL hm i hf hfind hw
  have hz1r2 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
    memZtransRtransSpine L hL hgn hunL hta hm (i + 1) hf
  -- trans (z₁, y₀)：界 = z₁ < w ≤ y₀（r₁ 上）
  have hT2 := transIndexfSucSpine L hL hta hgn hunL hm i hfi hy0r1 hz1r1
    hy0r2 hz1r2 hzy0
  -- A：indexf_add_left[z1; d; y0; r2]（界 = 前提 hle）
  have hA := indexfAddLeft hz1r2 hd2 hy0r2 hle
  -- B：indexf_add_right[z1; d; y0; r1]（界 = T2 与 T1 算术）
  have hB : indexf d (ytransSpine L N r x 0) (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x i) := by omega
  have hC := indexfAddRight hz1r1 hd1 hy0r1 hB
  omega

/-! ## §4 INDUCT_MAIN_RESULT（PBFLHET.hl:722-743） -/

/-- **HOL `Pbflhet.INDUCT_MAIN_RESULT`**（PBFLHET.hl:722-743）塔层 i 形：
`¬final(i+1) ∧ d ∈ r₂ ∧ indexf (l'z(i+1)) d r₂ ≤ indexf (l'z(i+1)) (l'y(0)) r₂
⇒ indexf (l'z(i+1)) d r₁ = indexf (l'z(i+1)) d r₂ ∧
indexf (l'z(i)) d r₁ ≤ indexf (l'z(i)) (l'y(0)) r₁ ∧ MEM d r₁`。
三合取直拼（HOL THENL 三支）。 -/
theorem inductMainResultSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd2 : d ∈ rtransSpine L N r x (i + 1))
    (hle : indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1))) :
    indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x i)
        = indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))
      ∧ indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
        ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
          (rtransSpine L N r x i)
      ∧ d ∈ rtransSpine L N r x i :=
  ⟨inductConstMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd2 hle,
   inductLeMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd2 hle,
   inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd2 hle⟩

/-! ## §5 INDUCT_CONST_MAIN_RESULT_TWO（PBFLHET.hl:749-789） -/

/-- **HOL `Pbflhet.INDUCT_CONST_MAIN_RESULT_TWO`**（PBFLHET.hl:749-789）
塔层 i 形：`¬final(i+1) ∧ d, d1 ∈ r₂ ∧ indexf (l'z(i+1)) d r₂ ≤
indexf (l'z(i+1)) (l'y(0)) r₂ ∧ indexf (l'z(i+1)) d1 r₂ ≤
indexf (l'z(i+1)) d r₂ ⇒ indexf d1 d r₁ = indexf d1 d r₂`。
证 = INDUCT_CONST 双实例（d / d1，d1 的界由前提链 le_trans）+
indexf_add_left r₂（界 = hle1）+ INDUCT_MEM 双实例 + indexf_add_left r₁
（界由 ③ 双实例方程算术）+ omega。 -/
theorem inductConstMainResultTwoSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d d1 : ℕ × ℕ} (hd2 : d ∈ rtransSpine L N r x (i + 1))
    (hd12 : d1 ∈ rtransSpine L N r x (i + 1))
    (hle : indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1)))
    (hle1 : indexf (ztransSpine L N r x (i + 1)) d1
        (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))) :
    indexf d1 d (rtransSpine L N r x i)
      = indexf d1 d (rtransSpine L N r x (i + 1)) := by
  have hC1 := inductConstMainResultSpine L hL hta hgn hunL hm i hf hfind hw
    hd2 hle
  have hle1' : indexf (ztransSpine L N r x (i + 1)) d1
        (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1)) := le_trans hle1 hle
  have hC2 := inductConstMainResultSpine L hL hta hgn hunL hm i hf hfind hw
    hd12 hle1'
  have hz1r2 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
    memZtransRtransSpine L hL hgn hunL hta hm (i + 1) hf
  have hA := indexfAddLeft hz1r2 hd12 hd2 hle1
  have hz1r1 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x i :=
    ztranSucInRtransSpine L hL hta hgn hunL hm i hf hfind hw
  have hd1 : d ∈ rtransSpine L N r x i :=
    inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd2 hle
  have hd11 : d1 ∈ rtransSpine L N r x i :=
    inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd12 hle1'
  have hB := indexfAddLeft hz1r1 hd11 hd1 (by omega)
  omega

/-! ## §6 INDUCT_LE_MAIN_RESULT_TWO（PBFLHET.hl:793-844） -/

/-- **HOL `Pbflhet.INDUCT_LE_MAIN_RESULT_TWO`**（PBFLHET.hl:793-844）塔层
i 形：`¬final(i+1) ∧ d, d1 ∈ r₂ ∧ indexf (l'z(i+1)) d r₂ ≤
indexf (l'z(i+1)) (l'y(0)) r₂ ∧ indexf (l'z(i+1)) d1 r₂ ≤
indexf (l'z(i+1)) d r₂ ⇒ indexf (l'z(i)) d r₁ ≤ indexf (l'z(i)) (l'y(0)) r₁
∧ indexf (l'z(i)) d1 r₁ ≤ indexf (l'z(i)) d r₁`。
证 = INDUCT_LE 双实例 + indexf_add_left r₁/r₂ 四方程 + trans_indexf_suc
双实例 + omega（d→y₀ ≤ d1→y₀ ⟹ z→d1 ≤ z→d）。 -/
theorem inductLeMainResultTwoSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d d1 : ℕ × ℕ} (hd2 : d ∈ rtransSpine L N r x (i + 1))
    (hd12 : d1 ∈ rtransSpine L N r x (i + 1))
    (hle : indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1)))
    (hle1 : indexf (ztransSpine L N r x (i + 1)) d1
        (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))) :
    indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
        ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
          (rtransSpine L N r x i)
      ∧ indexf (ztransSpine L N r x i) d1 (rtransSpine L N r x i)
        ≤ indexf (ztransSpine L N r x i) d (rtransSpine L N r x i) := by
  have hL1 := inductLeMainResultSpine L hL hta hgn hunL hm i hf hfind hw
    hd2 hle
  have hle1' : indexf (ztransSpine L N r x (i + 1)) d1
        (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1)) := le_trans hle1 hle
  have hL2 := inductLeMainResultSpine L hL hta hgn hunL hm i hf hfind hw
    hd12 hle1'
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    finalListInductSpine L N r x i hf
  have hzr1 : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hfi
  have hz1r2 : ztransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
    memZtransRtransSpine L hL hgn hunL hta hm (i + 1) hf
  have hd11 : d1 ∈ rtransSpine L N r x i :=
    inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd12 hle1'
  have hd1 : d ∈ rtransSpine L N r x i :=
    inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd2 hle
  have hy0r1 : ytransSpine L N r x 0 ∈ rtransSpine L N r x i :=
    (propertiesOfYtrans0Spine L hL hta hgn hunL hm i hfind hw hfi).2.2.2
  have hy0r2 : ytransSpine L N r x 0 ∈ rtransSpine L N r x (i + 1) :=
    (propertiesOfYtrans0Spine L hL hta hgn hunL hm (i + 1) hfind hw hf).2.2.2
  -- r₁ 上两方程：z→d1 + d1→y₀ = z→y₀、z→d + d→y₀ = z→y₀
  have hA1 := indexfAddLeft hzr1 hd11 hy0r1 hL2
  have hA2 := indexfAddLeft hzr1 hd1 hy0r1 hL1
  -- trans 双实例：d1→y₀ / d→y₀ 的 r₁↔r₂ 不变（界 = hL2 / hL1）
  have hT1 := transIndexfSucSpine L hL hta hgn hunL hm i hfi hy0r1 hd11
    hy0r2 hd12 hL2
  have hT2 := transIndexfSucSpine L hL hta hgn hunL hm i hfi hy0r1 hd1
    hy0r2 hd2 hL1
  -- r₂ 上两方程：z₁→d1 + d1→y₀ = z₁→y₀、z₁→d + d→y₀ = z₁→y₀
  have hB1 := indexfAddLeft hz1r2 hd12 hy0r2 hle1'
  have hB2 := indexfAddLeft hz1r2 hd2 hy0r2 hle
  exact ⟨hL1, by omega⟩

/-! ## §7 INDUCT_MAIN_RESULT_TWO（PBFLHET.hl:849-882） -/

/-- **HOL `Pbflhet.INDUCT_MAIN_RESULT_TWO`**（PBFLHET.hl:849-882）塔层 i 形：
`¬final(i+1) ∧ d, d1 ∈ r₂ ∧ indexf (l'z(i+1)) d r₂ ≤
indexf (l'z(i+1)) (l'y(0)) r₂ ∧ indexf (l'z(i+1)) d1 r₂ ≤
indexf (l'z(i+1)) d r₂ ⇒ indexf (l'z(i)) d r₁ ≤ indexf (l'z(i)) (l'y(0)) r₁
∧ indexf (l'z(i)) d1 r₁ ≤ indexf (l'z(i)) d r₁ ∧
indexf d1 d r₁ = indexf d1 d r₂ ∧ MEM d r₁ ∧ MEM d1 r₁`。
五合取直拼（⑥ ⑤ INDUCT_MEM 双实例）。 -/
theorem inductMainResultTwoSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d d1 : ℕ × ℕ} (hd2 : d ∈ rtransSpine L N r x (i + 1))
    (hd12 : d1 ∈ rtransSpine L N r x (i + 1))
    (hle : indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) (ytransSpine L N r x 0)
        (rtransSpine L N r x (i + 1)))
    (hle1 : indexf (ztransSpine L N r x (i + 1)) d1
        (rtransSpine L N r x (i + 1))
      ≤ indexf (ztransSpine L N r x (i + 1)) d (rtransSpine L N r x (i + 1))) :
    indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
        ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
          (rtransSpine L N r x i)
      ∧ indexf (ztransSpine L N r x i) d1 (rtransSpine L N r x i)
        ≤ indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
      ∧ indexf d1 d (rtransSpine L N r x i)
        = indexf d1 d (rtransSpine L N r x (i + 1))
      ∧ d ∈ rtransSpine L N r x i
      ∧ d1 ∈ rtransSpine L N r x i := by
  obtain ⟨h1, h2⟩ := inductLeMainResultTwoSpine L hL hta hgn hunL hm i hf
    hfind hw hd2 hd12 hle hle1
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · exact inductConstMainResultTwoSpine L hL hta hgn hunL hm i hf hfind hw
      hd2 hd12 hle hle1
  · exact inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd2 hle
  · exact inductMemMainResultSpine L hL hta hgn hunL hm i hf hfind hw hd12
      (le_trans hle1 hle)

/-! ## §8 PBFLHET_ALL（PBFLHET.hl:888-923） -/

/-- **HOL `Pbflhet.PBFLHET_ALL`**（PBFLHET.hl:888-923）塔层 i 形
（ri 内联为 `rtransSpine L N r x i`，w 前提省去——结论不含 w，等价重述）：
`MEM d ri ∧ MEM d1 ri ∧ ¬final ri ∧ indexf (l'z(i)) d ri ≤
indexf (l'z(i)) (l'y(0)) ri ∧ indexf (l'z(i)) d1 ri ≤ indexf (l'z(i)) d ri
⇒ ∀ t ≤ i, MEM d (rtrans t) ∧ MEM d1 (rtrans t) ∧
indexf (l'z(t)) d (rtrans t) ≤ indexf (l'z(t)) (l'y(0)) (rtrans t) ∧
indexf (l'z(t)) d1 (rtrans t) ≤ indexf (l'z(t)) d (rtrans t) ∧
indexf d1 d (rtrans t) = indexf d1 d (rtrans i)`。
证 = 对差值 m := i − t 归纳（HOL INDUCT_REV 翻转；照
finalListInduct1Spine 约定）：零支即前提；步支 FINAL_LIST_INDUCT1
（¬final 下传 @i−SUC m+1）+ ⑦ @j:=i−SUC m。 -/
theorem pbflhetAllSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {d d1 : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x i)
    (hd1 : d1 ∈ rtransSpine L N r x i)
    (hle : indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
        (rtransSpine L N r x i))
    (hle1 : indexf (ztransSpine L N r x i) d1 (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)) :
    ∀ t, t ≤ i →
      d ∈ rtransSpine L N r x t ∧ d1 ∈ rtransSpine L N r x t
        ∧ indexf (ztransSpine L N r x t) d (rtransSpine L N r x t)
            ≤ indexf (ztransSpine L N r x t) (ytransSpine L N r x 0)
              (rtransSpine L N r x t)
        ∧ indexf (ztransSpine L N r x t) d1 (rtransSpine L N r x t)
            ≤ indexf (ztransSpine L N r x t) d (rtransSpine L N r x t)
        ∧ indexf d1 d (rtransSpine L N r x t)
          = indexf d1 d (rtransSpine L N r x i) := by
  have key : ∀ m, m ≤ i →
      d ∈ rtransSpine L N r x (i - m) ∧ d1 ∈ rtransSpine L N r x (i - m)
        ∧ indexf (ztransSpine L N r x (i - m)) d (rtransSpine L N r x (i - m))
            ≤ indexf (ztransSpine L N r x (i - m)) (ytransSpine L N r x 0)
              (rtransSpine L N r x (i - m))
        ∧ indexf (ztransSpine L N r x (i - m)) d1 (rtransSpine L N r x (i - m))
            ≤ indexf (ztransSpine L N r x (i - m)) d (rtransSpine L N r x (i - m))
        ∧ indexf d1 d (rtransSpine L N r x (i - m))
          = indexf d1 d (rtransSpine L N r x i) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero]
      exact ⟨hd, hd1, hle, hle1, rfl⟩
    | succ m ih =>
      intro hm1
      obtain ⟨hdm, hd1m, hlem, hle1m, heqm⟩ := ih (by omega)
      have hj : i - m = (i - (m + 1)) + 1 := by omega
      rw [hj] at hdm hd1m hlem hle1m heqm
      have hfj : ¬ finalListSpine L (rtransSpine L N r x ((i - (m + 1)) + 1)) :=
        finalListInduct1Spine L N r x i hf _ (by omega)
      obtain ⟨hA, hB, hC, hD, hE⟩ :=
        inductMainResultTwoSpine L hL hta hgn hunL hm (i - (m + 1)) hfj
          rfl rfl hdm hd1m hlem hle1m
      exact ⟨hD, hE, hA, hB, hC.trans heqm⟩
  intro t ht
  have h := key (i - t) (by omega)
  rw [Nat.sub_sub_self ht] at h
  exact h

/-! ## §9 PBFLHET（PBFLHET.hl:928-948） -/

/-- **HOL `Pbflhet.PBFLHET`**（PBFLHET.hl:928-948）塔层 i 形（ri 内联，
w 前提省去）：`MEM d ri ∧ ¬final ri ∧ indexf (l'z(i)) d ri ≤
indexf (l'z(i)) (l'y(0)) ri ⇒ MEM d r ∧
indexf (l'z(i)) d ri = indexf (l'z(i)) d r`。
证 = ⑧ @t:=0、d1 := l'z(i)（mem_ztrans_rtrans@i + indexf_refl 供第二
前提）+ rtrans 0 ≡ r 定义级。 -/
theorem pbflhetSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {d : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x i)
    (hle : indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x 0)
        (rtransSpine L N r x i)) :
    d ∈ r ∧ indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
      = indexf (ztransSpine L N r x i) d r := by
  have hz : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hf
  have hle1 : indexf (ztransSpine L N r x i) (ztransSpine L N r x i)
        (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) d (rtransSpine L N r x i) := by
    rw [indexfRefl hz]
    exact Nat.zero_le _
  obtain ⟨hmem, -, -, -, heq⟩ :=
    pbflhetAllSpine L hL hta hgn hunL hm i hf hd hz hle hle1 0 (Nat.zero_le i)
  rw [show rtransSpine L N r x 0 = r from rfl] at hmem heq
  exact ⟨hmem, heq.symm⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.wBetwnZtransYtran0Spine
#print axioms Kepler.Text.TameSpine.inductLeMainResultSpine
#print axioms Kepler.Text.TameSpine.inductConstMainResultSpine
#print axioms Kepler.Text.TameSpine.inductMainResultSpine
#print axioms Kepler.Text.TameSpine.inductConstMainResultTwoSpine
#print axioms Kepler.Text.TameSpine.inductLeMainResultTwoSpine
#print axioms Kepler.Text.TameSpine.inductMainResultTwoSpine
#print axioms Kepler.Text.TameSpine.pbflhetAllSpine
#print axioms Kepler.Text.TameSpine.pbflhetSpine
