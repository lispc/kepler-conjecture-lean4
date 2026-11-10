/-
  Kepler.Text.TameSpine.Reduction3Pbflhet3 — tame-corr nb5：nc5 收口（件 0 槽消 +
  OHCGKFU 主件 V0 移植 + 塔层薄包装 + trans_indexf_suc）。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ §0 件 0（快件）：`ztransSucInZtanW`——nb4 `ztransSucInZtanWSpine`
  │    （05e44be7）的 hPw 槽消去。**对形结论**：nb4 槽形自带 `∀ d' ∈ r'`
  │    （MEM 前提在内），与 `pwssratSpine@0`（Reduction3Pwssrat:65，
  │    `8527c357`）逐字同形——`rtransSpine … 0` ≡ `r`、`0 + 1` ≡ `1`、
  │    `ztransSpine … 0` ≡ `lZSpine …`（iterate 零支定义级）——直接供给
  │    路线，零无 MEM 变体需求（工单两条备选取第一条）。
  │ §1 件 1：`ohcgkfuMainV0Spine`（HOL Ohcgkfu.OHCGKFU_concl
  │    OHCGKFU.hl:162-280 的 i=0 spine 形移植；四步方案执行）：
  │    final 二分（final 支 rtrans1 = r）→ rtransCat 展开 → 窗口支反证
  │    （indexf_betwn_eq + indexf_n + indexfYtransSucLp + fListPowYtransNotMem
  │    极小性——全在库，零新增几何）→ 非窗口支 head 锚私件两枚
  │    （indexfHead/indexfHeadAppend）+ d = l'z / betwn r l'z l'y / d = l'y
  │    三支位置账（indexfRefl / indexlBetwn+sizeBetwn / betwnCases+antisym
  │    弧互斥 omega）。
  │ §2 件 2：`ohcgkfuTowerSpine`（OHCGKFU.hl:162 通用 i 形＝V0 塔层薄包装：
  │    aqiunpp3 供标记件 + rtransSuccSpine 折叠）+
  │    `transIndexfSucSpine`（PBFLHET.hl:536 ＝ OHCGKFU 塔层形双实例 +
  │    ztransInSucSpine（nb2）+ indexf_add_left×2 + omega）。
  └────────────────────────────────────────────────────────────────

  ┌─ 冻结件（陈述 + 消费树 + 估行 + 卡点）────────────────────────
  │ `w_betwn_ztrans_ytran0`（PBFLHET.hl:567-630，64 HOL 行）：**续冻**。
  │   陈述（塔层 i，全在 r₁ 上）：indexf (l'z(i)) w r₁ ≤ indexf (l'z(i))
  │   (l'y(0)) r₁ ∧ indexf (l'z(i)) (l'y(0)) r₁ ≤ indexf (l'z(i)) (l'y(i)) r₁。
  │   已备消费件：propertiesOfYtrans0Spine / nextMarkCaseMemSpine /
  │   indexfConstLeIndexfYtransSpine（nb3）+ ytransMemRtrans + hqymrtx3List
  │   + TameList3 全族——零外部缺口。
  │   卡点（nb4 卡片的深化）：两合取都需 l'y(0) 在 r₁ 上的环弧序
  │   （z→w→l'y(0)→l'y(i)）。本轮尝试的反证路线仍有缺口：假设
  │   y0 ∈ betwn r₁ y l'z（loop 余弧）时，其面位置 ≤ l'm（properties
  │   conj3）与 notInNtrans（face-(y,z) 开弧无 loop 点，nb1 件）联合
  │   只排除 y0 ∈ face-(y,z) 开弧，不排除 y0 ∈ loop-(y,z) ∩ face-
  │   [w→y] 段——该段 loop/face 位置账需 l'p 极小性的 second application
  │   或 z 的 HQYMRTX 位置引理，单轮未能闭合。估行（含弧序引理）：
  │   80–140。消费面：INDUCT_LE_MAIN_RESULT（nc6 首件）+
  │   betwn_ztran_ytrans_suc_const（J4 关键路径）——nc6 仍由本件门控。
  │ 余量 nc6 归纳五件：门控于上件（INDUCT_LE 首件直接消费
  │   w_betwn_ztrans_ytran0）+ trans_indexf_suc（本笔件 2 已解锁）——
  │   本轮不落（前件缺一）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ pwssratSpine / memZtransRtransSpine / ytransMemRtrans / rtransCat /
  │ rtransSuccSpine / indexfYtransSucLp / fListPowYtransNotMem /
  │ markedLemmaYzInFace / hqymrtx3List / ztransInSucSpine /
  │ indexfConstLeIndexfYtransSpine / TameList3 indexf-betwn 族）同世界
  │ 零混合；私件（indexfHead/indexfHeadAppend）泛 α 纯算术；零 Dart
  │ 载体件。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Pbflhet2
import Kepler.Text.TameSpine.Reduction3Pbflhet1
import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans2
import Kepler.Text.TameSpine.Reduction3QcdvkeaTower
import Kepler.Text.TameSpine.Reduction3Pwssrat
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

/-! ## §0 件 0：ztransSucInZtanW 槽消（PWSSRAT 主件已在库） -/

/-- **HOL `Pbflhet.ztrans_suc_in_ztran_w`**（PBFLHET.hl:462-511）塔层 i 形
（无条件形）：`¬final(i+1) ⇒ indexf (l'z(i)) (l'z(i+1)) r₁ <
indexf (l'z(i)) w r₁`。
证 = nb4 `ztransSucInZtanWSpine`（05e44be7）+ hPw 槽消：槽形自带
`∀ d' ∈ r'` 与 `pwssratSpine@0`（`8527c357`，PWSSRAT.hl:584 逐字）同形
（`rtransSpine … 0` ≡ `r`、`0 + 1` ≡ `1`、`ztransSpine … 0` ≡ `lZSpine …`
iterate 零支定义级）——**直接供给**（工单两条备选取第一条：槽形不强于
pwssratSpine@0，无 MEM 变体需求）。 -/
theorem ztransSucInZtranWSpineClosed (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf (ztransSpine L N r x i) (ztransSpine L N r x (i + 1))
        (rtransSpine L N r x i)
      < indexf (ztransSpine L N r x i) w (rtransSpine L N r x i) :=
  ztransSucInZtanWSpine L hL hta hgn hunL hm i hf hfind hw
    (fun hm' hf' d' hd' => pwssratSpine L hL hta hgn hm' 0 hd' hf')

/-! ## §1 件 1：OHCGKFU 主件 V0 移植 -/

/-- 私件（head 锚 indexf 折叠为 idxOf）：`u.idxOf h = 0 ∧ d ∈ u ⇒
indexf h d u = u.idxOf d`。（indexf 定义展开 + mod_eq_of_lt。） -/
private theorem indexfHead {α : Type*} [BEq α] [LawfulBEq α] {u : List α}
    {h d : α} (hhead : u.idxOf h = 0) (hmem : d ∈ u) :
    indexf h d u = u.idxOf d := by
  have hdm : u.idxOf d < u.length := List.idxOf_lt_length_iff.mpr hmem
  have hhu : h ∈ u := List.idxOf_lt_length_iff.mp (by rw [hhead]; omega)
  rw [indexf, if_pos ⟨hhu, hmem⟩, hhead, Nat.sub_zero, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hdm

/-- 私件（HOL `Ohcgkfu.indexf_append_not` 的 head 锚形）：`u.idxOf h = 0 ∧
d ∈ u ∧ d ∉ v` ⇒ `indexf h d (u ++ v) = indexf h d u`（尾延表不变）。 -/
private theorem indexfHeadAppend {α : Type*} [BEq α] [LawfulBEq α]
    {u v : List α} {h d : α}
    (hhead : u.idxOf h = 0) (hmem : d ∈ u) (hnot : d ∉ v) :
    indexf h d (u ++ v) = indexf h d u := by
  have hdm : u.idxOf d < u.length := List.idxOf_lt_length_iff.mpr hmem
  have hhu : h ∈ u := List.idxOf_lt_length_iff.mp (by rw [hhead]; omega)
  have hhuv : h ∈ u ++ v := List.mem_append.mpr (Or.inl hhu)
  have hduv : d ∈ u ++ v := List.mem_append.mpr (Or.inl hmem)
  rw [indexfHead hhead hmem, indexf, if_pos ⟨hhuv, hduv⟩,
    List.idxOf_append_of_mem hmem, List.idxOf_append_of_mem hhu, hhead,
    Nat.sub_zero, List.length_append]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- **HOL `Ohcgkfu.OHCGKFU_concl`**（OHCGKFU.hl:162-168）的 i=0 spine 形：
`MEM d r ∧ MEM d (rtrans 1) ⇒ indexf (l'z) d r = indexf (l'z) d (rtrans 1)`。
证（与 HOL 同构，final 二分）：final 支 rtrans1 = r 定义级收口；¬final 支
= rtransCat 展开 + 窗口支反证（d ∈ betwn f(l'y) l'z ⟹ indexf (l'y) d f <
indexf (l'y) l'z f = SUC l'p（indexfYtransSucLp）⟹ d = f^(SUC (PRE idx))
(l'y) ∈ r 与 PRE idx < l'p 违 fListPowYtransNotMem 极小性）+ 非窗口支
indexfHeadAppend/indexfHead（私件）+ d = l'z / d ∈ betwn r l'z l'y / d = l'y
三支位置账（indexfRefl / indexlBetwn+sizeBetwn / 弧互斥 antisym+add_betwn
omega）。**零新增几何**：窗口反证全部消费在库件（indexfYtransSucLp /
fListPowYtransNotMem / indexf_betwn_eq / indexf_n / markedLemmaYzInFace）。
HOL 原文无 ¬final 前提，本形逐字同（final 支平凡）。 -/
theorem ohcgkfuMainV0Spine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {d : ℕ × ℕ} (hd : d ∈ r) (hd1 : d ∈ rtransSpine L N r x 1) :
    indexf (lZSpine L N r x) d r
      = indexf (lZSpine L N r x) d (rtransSpine L N r x 1) := by
  by_cases hfin : finalListSpine L r
  · have h1' : rtransSpine L N r x 1 = r :=
      congrArg Prod.snd (finalSuccIdSpine L N r x 0 hfin)
    rw [h1']
  · have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
    have hyl : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hfin
    have hzl : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hfin
    have hzy : lZSpine L N r x ≠ lYSpine L r x :=
      Ne.symm (hqymrtx3List L hL hgn hunL hm hfin)
    obtain ⟨hyf, hzf⟩ := markedLemmaYzInFace L hL hgn hunL hm hfin
    have hxd : x ∈ listOfDarts L :=
      normalListListOfDarts hm.1.2.1 x
        (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
    have hcong : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
      findFaceDarts_congr_of_mem hL.1 hxd hyf
    -- r₂ 展开为 (([z] ++ B) ++ [y]) ++ C（rtransCat；面锚归 findFaceDarts L x）
    rw [rtransCat L N r x hfin hrnd, hcong] at hd1 ⊢
    by_cases hwin : d ∈ between (findFaceDarts L x) (lYSpine L r x)
        (lZSpine L N r x)
    · -- 窗口支：d ∈ betwn f (l'y) (l'z) 反证（l'p 极小性）
      exfalso
      have hyd : lYSpine L r x ∈ listOfDarts L := mem_darts_of_mem_findFace L hyf
      have hyL1 : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
        (dart_in_face L (lYSpine L r x)).mpr hyd
      have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
      have hne1 : lYSpine L r x ≠ lZSpine L N r x :=
        hqymrtx3List L hL hgn hunL hm hfin
      have hmem : d ∈ findFaceDarts L x := betwnMem hwin
      obtain ⟨hp1, hp2⟩ := (indexfBetwnEq hne1 hfnd hyf hzf).mp hwin
      have hsuc := indexfYtransSucLp L hL hgn hunL hm hfin
      rw [hcong] at hsuc
      have hpos : indexf (lYSpine L r x) d (findFaceDarts L x) - 1
          < lPSpine L N r x := by omega
      have hmin := fListPowYtransNotMem L hL hm
        (indexf (lYSpine L r x) d (findFaceDarts L x) - 1) hpos
      have hstep := indexfN hyf hmem hfnd
      have hfpow := fListPowEqNextElPow L hL (lYSpine L r x) hyL1
        (indexf (lYSpine L r x) d (findFaceDarts L x) - 1 + 1)
      rw [hcong] at hfpow
      have heq1 : indexf (lYSpine L r x) d (findFaceDarts L x) - 1 + 1
          = indexf (lYSpine L r x) d (findFaceDarts L x) :=
        Nat.sub_add_cancel (by omega)
      rw [heq1, hstep] at hfpow
      have hmem' : (fList L)^[indexf (lYSpine L r x) d (findFaceDarts L x)
          - 1 + 1] (lYSpine L r x) ∈ r := by
        rw [heq1, hfpow]
        exact hd
      exact hmin hmem'
    · -- 非窗口支：d ∈ A' = ([z]++B)++[y]，head 锚 indexf 对尾延表不变
      have hdA : d ∈ [lZSpine L N r x] ++ between r (lZSpine L N r x)
          (lYSpine L r x) ++ [lYSpine L r x] := by
        rcases List.mem_append.mp hd1 with h | hC
        · exact h
        · exact absurd hC hwin
      have hhead0 : ([lZSpine L N r x] ++ between r (lZSpine L N r x)
            (lYSpine L r x) ++ [lYSpine L r x]).idxOf (lZSpine L N r x) = 0 := by
        simp
      rw [indexfHeadAppend hhead0 hdA hwin, indexfHead hhead0 hdA]
      -- 目标：indexf l'z d r = A'.idxOf d；按 d 在 A' 中的三支定位
      rcases List.mem_append.mp hdA with hAB | hAy
      · rcases List.mem_append.mp hAB with hAz | hB
        · -- d = l'z：两侧为 0
          rw [List.mem_singleton] at hAz
          rw [hAz, indexfRefl hzl]
          simp
        · -- d ∈ betwn r l'z l'y：indexl_betwn 位置账
          have hidx := indexlBetwn hrnd hzl hyl hB
          have hdz : d ∉ [lZSpine L N r x] := by
            intro hc
            rw [List.mem_singleton] at hc
            rw [hc] at hB
            exact notBetwn1 hrnd hyl hB
          rw [List.idxOf_append_of_mem hAB, List.idxOf_append_of_notMem hdz,
            List.length_singleton, ← hidx]
          omega
      · -- d = l'y：A'.idxOf = 1 + |B| = indexf l'z l'y r（sizeBetwn）
        rw [List.mem_singleton] at hAy
        have hBlen := sizeBetwn hrnd hzl hyl hzy
        have hny : lYSpine L r x ∉ [lZSpine L N r x]
            ++ between r (lZSpine L N r x) (lYSpine L r x) := by
          intro hc
          rcases List.mem_append.mp hc with h | h
          · rw [List.mem_singleton] at h
            exact hzy h.symm
          · exact notBetwn2 hrnd h
        have h0 : ([lYSpine L r x]).idxOf (lYSpine L r x) = 0 := by simp
        have hpos : 0 < indexf (lZSpine L N r x) (lYSpine L r x) r := by
          by_contra hc
          exact hzy (indexfZeroEq hzl hyl (by omega))
        rw [hAy, List.idxOf_append_of_notMem hny, h0, List.length_append,
          List.length_singleton, hBlen]
        omega

/-! ## §2 件 2：OHCGKFU 塔层薄包装 + trans_indexf_suc -/

/-- **HOL `Ohcgkfu.OHCGKFU_concl`**（OHCGKFU.hl:162）通用 i 塔层形（逐字，
无 ¬final 前提）＝ V0 塔层薄包装：`MEM d (rtrans i) ∧ MEM d (rtrans(i+1)) ⇒
indexf (l'z(i)) d (rtrans i) = indexf (l'z(i)) d (rtrans(i+1))`。
标记件由塔层 i 的 aqiunpp3 供给，折叠经 rtransSuccSpine。 -/
theorem ohcgkfuTowerSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    {d : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x i)
    (hd1 : d ∈ rtransSpine L N r x (i + 1)) :
    indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
      = indexf (ztransSpine L N r x i) d (rtransSpine L N r x (i + 1)) := by
  rw [rtransSuccSpine L N r x i] at hd1 ⊢
  exact ohcgkfuMainV0Spine L hL hgn hunL (aqiunpp3 L hL i hta hgn hm) hd hd1

/-- **HOL `Pbflhet.trans_indexf_suc`**（PBFLHET.hl:536）塔层 i 形：
`¬final(i) ∧ d, d1 ∈ r₁ ∩ r₂ ∧ indexf (l'z(i)) d1 r₁ ≤ indexf (l'z(i)) d r₁ ⇒
indexf d1 d r₁ = indexf d1 d r₂`。
证 = OHCGKFU 塔层形双实例（z 锚在 r₁/r₂ 间不变）+ memZtransRtransSpine
（nb1：l'z(i) ∈ r₁）+ ztransInSucSpine（nb2：l'z(i) ∈ r₂）+
indexf_add_left×2 + omega。 -/
theorem transIndexfSucSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {d d1 : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x i)
    (hd1 : d1 ∈ rtransSpine L N r x i)
    (hd2 : d ∈ rtransSpine L N r x (i + 1))
    (hd12 : d1 ∈ rtransSpine L N r x (i + 1))
    (hle : indexf (ztransSpine L N r x i) d1 (rtransSpine L N r x i)
      ≤ indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)) :
    indexf d1 d (rtransSpine L N r x i)
      = indexf d1 d (rtransSpine L N r x (i + 1)) := by
  have hOd := ohcgkfuTowerSpine L hL hta hgn hunL hm i hd hd2
  have hOd1 := ohcgkfuTowerSpine L hL hta hgn hunL hm i hd1 hd12
  have hzl1 : lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
      ∈ rtransSpine L N r x i := memZtransRtransSpine L hL hgn hunL hta hm i hf
  have hzl2 : lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
      ∈ rtransSpine L N r x (i + 1) := ztransInSucSpine L hL hta hgn hm i hf
  rw [show ztransSpine L N r x i
      = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl]
    at hle hOd hOd1
  have hE1 := indexfAddLeft hzl1 hd1 hd hle
  have hE2 := indexfAddLeft hzl2 hd12 hd2 (by omega)
  omega

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.ztransSucInZtranWSpineClosed
#print axioms Kepler.Text.TameSpine.ohcgkfuMainV0Spine
#print axioms Kepler.Text.TameSpine.ohcgkfuTowerSpine
#print axioms Kepler.Text.TameSpine.transIndexfSucSpine
