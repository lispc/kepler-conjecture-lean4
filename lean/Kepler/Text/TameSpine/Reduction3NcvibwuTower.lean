/-
  Kepler.Text.TameSpine.Reduction3NcvibwuTower — tame-corr nb2：NCVIBWU 主件
  （HOL Ncvibwu.NCVIBWU :1463 与 NCVIBWU2 :425 / NCVIBWU3 :1132）的
  **通用 i 塔层 spine 形**——aq13 `deebb37e` 九槽全闭后的薄包装收口。

  ┌─ 归属对账（(c) 三问的机器证据·正件）─────────────────────────────
  │ ①（三问之一）**通用 i 塔 = V0 件 + 塔层 AQIUNPP3，成立**：本文件
  │    三件全部由 `ncvibwuV0FullSpine`（Reduction3NcvibwuIndexMain:823，
  │    任意 marked 态双半装配）在塔层 `(ntransSpine i, rtransSpine i)`
  │    实例化得到：
  │    · 标记件由塔层 i 的 `aqiunpp3`（TameList17）供给；
  │    · `l'z(i) = lZSpine (ntransSpine i) (rtransSpine i) x` 与
  │      折叠后状态 0 的 l'z **定义级同项**（delta）；
  │    · `rtrans(i+1) = rtransSpine (ntransSpine i) (rtransSpine i) x 1`
  │      经 `rtransSuccSpine`（Reduction3LnrxInductionSpine）折叠。
  │ ②（三问之二）**薄包装行数**：三件合计 ≤ 45 行（陈述 ~36 + 证明
  │    各 1–2 行）；即 N-A 主塔的 NCVIBWU 层从"6–10 波"坍缩为一页。
  │ ③（三问之三）**不卡**：NCVIBWU 家族零剩余；真剩余 =
  │    QCDVKEA V0 本体（aq13 在飞，续 822 续派，估 80–120）+ PBFLHET
  │    章中部 23 件（其中单步件可同法薄包装，归纳件需真塔归纳）。
  │ DIFFERS：HOL 主件由 NCVIBWU2（j<）∨ NCVIBWU3（j=）拼装；本形由
  │ V0 双半直得 `j ≤` 全形，2/3 件反降为界形推论。
  │ 编译基线：≥ `deebb37e`（消费 ncvibwuV0FullSpine；对更早基线本
  │ 文件不编，主 patch 的 Reduction3KbwpbhqNtrans2.lean 保持 `1a057cfb`
  │ 基线可编）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件
  │ ncvibwuV0FullSpine / aqiunpp3 / rtransSuccSpine 同世界零混合；
  │ 本文件零 Dart 载体件。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans
import Kepler.Text.TameSpine.Reduction3NcvibwuIndexMain

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)

/-! ## NCVIBWU 主件通用 i 塔层形（HOL NCVIBWU.hl:1463） -/

/-- **HOL `Ncvibwu.NCVIBWU_concl`**（NCVIBWU.hl:1463）的 spine 塔层 i 形：
`j ≤ indexf w (l'z(i)) f ⇒ (next_el f)^j w ∈ rtrans(i+1) ∧
indexf w ((next_el f)^j w) (rtrans(i+1)) = j`。
证 = ncvibwuV0FullSpine 在塔层 (ntransSpine i, rtransSpine i) 直投 +
rtransSuccSpine 折叠（ztransSpine 的 l'z 项 delta 同项）。 -/
theorem ncvibwuTowerSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) {j : ℕ}
    (hj : j ≤ indexf w (ztransSpine L N r x i) f) :
    (nextEl f)^[j] w ∈ rtransSpine L N r x (i + 1)
      ∧ indexf w ((nextEl f)^[j] w) (rtransSpine L N r x (i + 1)) = j := by
  rw [rtransSuccSpine L N r x i]
  exact ncvibwuV0FullSpine L hL hgn (aqiunpp3 L hL i hta hgn hm) hf hfind hw hj

/-- **HOL `Ncvibwu.NCVIBWU2_concl`**（NCVIBWU.hl:425）塔层 i 界形
（j < indexf）：主件推论（Nat.le_of_lt）。 -/
theorem ncvibwu2TowerSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) {j : ℕ}
    (hj : j < indexf w (ztransSpine L N r x i) f) :
    (nextEl f)^[j] w ∈ rtransSpine L N r x (i + 1)
      ∧ indexf w ((nextEl f)^[j] w) (rtransSpine L N r x (i + 1)) = j :=
  ncvibwuTowerSpine L hL hta hgn hm i hf hfind hw (Nat.le_of_lt hj)

/-- **HOL `Ncvibwu.NCVIBWU3_concl`**（NCVIBWU.hl:1132）塔层 i 界形
（j = indexf）：主件推论（Nat.le_of_eq）。 -/
theorem ncvibwu3TowerSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) {j : ℕ}
    (hj : j = indexf w (ztransSpine L N r x i) f) :
    (nextEl f)^[j] w ∈ rtransSpine L N r x (i + 1)
      ∧ indexf w ((nextEl f)^[j] w) (rtransSpine L N r x (i + 1)) = j :=
  ncvibwuTowerSpine L hL hta hgn hm i hf hfind hw (Nat.le_of_eq hj)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.ncvibwuTowerSpine
#print axioms Kepler.Text.TameSpine.ncvibwu2TowerSpine
#print axioms Kepler.Text.TameSpine.ncvibwu3TowerSpine
