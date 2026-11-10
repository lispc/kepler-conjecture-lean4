/-
  Kepler.Text.TameSpine.Reduction3KbwpbhqPrev — tame-corr nb9：KBWPBHQ 章
  prev_el 侧前两件（KBWPBHQ :1246–:1406）。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ ① `prevElConstZtranRtransSpine`（KBWPBHQ.hl:1253-1353
  │    prev_el_const_ztran_rtrans）：¬final(i) ∧ marked ⇒
  │    prev_el rᵢ (l'z(i)) = prev_el r (l'z(i))。
  │    证（HOL 同构）：indexf_y_le_z_in_r + indexf_add_left ⟹ 0 < y→z；
  │    n := PRE (y→z)，d := (next_el rᵢ)^n y；indexf_n 给 next_el rᵢ d = z；
  │    退化支 w = z（与 y→z > 0 相抵）/ w = y（y0 = y ⟹ i = 0 定义级；
  │    i > 0 支 QCDVKEA@(i−1) + PPLHULJ@(i−1) 反证）后主支：
  │    indexf_antisym×2 界 ⟹ zi w ≤ yi w ⟹ indexf_add_right 给
  │    y→z + z→w = y→w；next_eq_rtrans_r 双实例（n / n+1）⟹ next_el r d = z；
  │    MEM_POWER_NEXT_EL（rᵢ / r）+ change_next_prev 双实例（rᵢ / r）
  │    两 prev 同归 d。
  │ ② `prevElBetwnZtranRtransSpine`（KBWPBHQ.hl:1357-1406
  │    prev_el_betwn_ztran_rtrans）：¬final(i) ∧ marked ∧ next_el f x = w ⇒
  │    prev_el rᵢ (l'z(i)) ∈ rᵢ ∧ indexf w (prev_el …) rᵢ < indexf w (l'z(i)) rᵢ
  │    ∧ indexf w (l'y(i)) rᵢ ≤ indexf w (prev_el …) rᵢ。
  │    证（HOL 同构）：① 的同一 d；MEM_POWER_NEXT_EL 给 d ∈ rᵢ；
  │    indexf_n[w;y;rᵢ] + indexf_lt_sizel + next_eln_indexf（n + w→y 指数）
  │    ⟹ indexf w d rᵢ = n + w→y，与 w→y / w→z 两个界收口。
  │ 在库复用：TameLp.prevEl_nextEl（:4921；`nextEl` 吃环境 BEq 实例，与
  │ spine 塔族同世界）。**BEq 世界记档**：`changeNextPrev`
  │ （Reduction3CoreSplitNormal:2293）与 `prevNextId` 只在
  │ `[DecidableEq α]` 上下文里绑定 `nextEl`（⇒ `instBEqOfDecidableEq`
  │ 世界），在 ℕ × ℕ 处与 spine 塔族的 `instBEqProd` 不同一，**不可直接
  │ 消费**（本轮实测 type mismatch 于 `nextEl` 的实例参）；故本文件改用
  │ `prevEl_nextEl`。链世界同题件 prevElBetwnZtranRtrans
  │ （Reduction5Kbwpbhq:149，haq 槽）为双载体孪生，非重落。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ ytransMemRtrans / memZtransRtransSpine / indexfYLeZInRSpine（nb7）/
  │ finalListInductSpine / propertiesOfYtrans0Spine / pnxvwfs1Spine /
  │ pnxvwfs2Spine / qcdvkeaTowerSpine / pplhuljV0 / indexfAntisym /
  │ indexfAddLeft / indexfAddRight / indexfN / nextElnIndexf /
  │ memPowerNextEl / changeNextPrev / nextEqRtransRSpine（nb8）/
  │ TameList3 indexf 族 / TameLp 面件）同世界零混合；零 Dart 载体件。
  │ 默认心跳、linter 全开。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqYtransConst
import Kepler.Text.TameSpine.Reduction3CoreSplitNormal

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts prevEl)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup)

/-! ## §1 prev_el_const_ztran_rtrans（KBWPBHQ.hl:1253-1353） -/

/-- **HOL `Kbwpbhq.prev_el_const_ztran_rtrans`**（KBWPBHQ.hl:1253-1353）
塔层 i 形：`¬final(i) ∧ marked ⇒ prev_el rᵢ (l'z(i)) = prev_el r (l'z(i))`。
证（HOL 同构；详见文件头 ①）。 -/
theorem prevElConstZtranRtransSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    prevEl (rtransSpine L N r x i) (ztransSpine L N r x i)
      = prevEl r (ztransSpine L N r x i) := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hyi : ytransSpine L N r x i ∈ rtransSpine L N r x i :=
    ytransMemRtrans L hL hgn hmr hf
  have hzi : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hf
  have hrnd : (rtransSpine L N r x i).Nodup :=
    (normalListUniqNonnil hmr.1.2.1 hmr.1.2.2.1).1
  have hwr : w ∈ rtransSpine L N r x i := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm i
  have hle := indexfYLeZInRSpine L hL hta hgn hm i hf hfind hw
  have hA := indexfAddLeft hwr hyi hzi (Nat.le_of_lt hle)
  have hpos : 0 < indexf (ytransSpine L N r x i) (ztransSpine L N r x i)
      (rtransSpine L N r x i) := by omega
  by_cases hwzi : w = ztransSpine L N r x i
  · -- 退化支 w = z：与 y→z > 0 相抵
    exfalso
    have h0 : indexf w (ztransSpine L N r x i) (rtransSpine L N r x i) = 0 := by
      rw [hwzi]
      exact indexfRefl hzi
    omega
  · by_cases hwyi : w = ytransSpine L N r x i
    · -- 退化支 w = y：先证 y0 = y，再分 i = 0 / i > 0
      have hyif : ytransSpine L N r x i ∈ f := by
        obtain ⟨hyf0, -, -⟩ :=
          pplhuljV0 L hL hgn hunL (aqiunpp3 L hL i hta hgn hm) hf
        rw [hfind] at hyf0
        exact hyf0
      have hP := propertiesOfYtrans0Spine L hL hta hgn hunL hm i hfind hw hf
      have hself : indexf w (ytransSpine L N r x i) f = 0 := by
        rw [hwyi]
        exact indexfRefl hyif
      have hy00 : indexf w (ytransSpine L N r x 0) f = 0 := by omega
      have h0r : indexf (ytransSpine L N r x i) (ytransSpine L N r x 0)
          (rtransSpine L N r x i) = 0 := by
        rw [← hwyi]
        have := hP.1
        omega
      have hy0 : ytransSpine L N r x 0 = ytransSpine L N r x i :=
        (indexfZeroEq hyi hP.2.2.2 h0r).symm
      cases i with
      | zero =>
        rw [show rtransSpine L N r x 0 = r from rfl]
      | succ j =>
        exfalso
        have hfj : ¬ finalListSpine L (rtransSpine L N r x j) :=
          finalListInductSpine L N r x j hf
        have hQ := qcdvkeaTowerSpine L hL hta hgn hm j hf hfind hw
        obtain ⟨-, -, hlt⟩ :=
          pplhuljV0 L hL hgn hunL (aqiunpp3 L hL j hta hgn hm) hfj
        rw [hfind] at hlt
        rw [hw] at hlt
        have hlt' : indexf w (ytransSpine L N r x j) f
            < indexf w (ztransSpine L N r x j) f := hlt
        have hyif1 : ytransSpine L N r x (j + 1) ∈ f := by
          obtain ⟨hyf1, -, -⟩ :=
            pplhuljV0 L hL hgn hunL (aqiunpp3 L hL (j + 1) hta hgn hm) hf
          rw [hfind] at hyf1
          exact hyf1
        have hQ0 : indexf w (ztransSpine L N r x j) f ≤ 0 := by
          have h := hQ
          rw [hwyi] at h
          have hz0 : indexf (ytransSpine L N r x (j + 1))
              (ytransSpine L N r x (j + 1)) f = 0 := indexfRefl hyif1
          omega
        omega
    · -- 主支：antisym 双实例 + add_right + next_eq 双实例 + change_next_prev 双实例
      have hanti_zi := indexfAntisym hwr hzi hwzi
      have hanti_yi := indexfAntisym hwr hyi hwyi
      have hzile : indexf (ztransSpine L N r x i) w (rtransSpine L N r x i)
          ≤ indexf (ytransSpine L N r x i) w (rtransSpine L N r x i) := by omega
      have hA3 := indexfAddRight hyi hzi hwr hzile
      obtain ⟨n, hn⟩ : ∃ n, indexf (ytransSpine L N r x i)
          (ztransSpine L N r x i) (rtransSpine L N r x i) = n + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      have hzn : (nextEl (rtransSpine L N r x i))^[n + 1]
          (ytransSpine L N r x i) = ztransSpine L N r x i := by
        rw [← hn]
        exact indexfN hyi hzi hrnd
      have hb_n : n ≤ indexf (ytransSpine L N r x i) w (rtransSpine L N r x i) := by
        omega
      have hb_s : n + 1 ≤ indexf (ytransSpine L N r x i) w
          (rtransSpine L N r x i) := by omega
      have hpow_n := nextEqRtransRSpine L hL hta hgn hunL hm i hf hfind hw
        (n := n) hb_n
      have hpow_s := nextEqRtransRSpine L hL hta hgn hunL hm i hf hfind hw
        (n := n + 1) hb_s
      have hmem_d : (nextEl (rtransSpine L N r x i))^[n]
          (ytransSpine L N r x i) ∈ rtransSpine L N r x i := memPowerNextEl hyi n
      have hnext_ri_d : nextEl (rtransSpine L N r x i)
          ((nextEl (rtransSpine L N r x i))^[n] (ytransSpine L N r x i))
          = ztransSpine L N r x i := by
        rw [← Function.iterate_succ_apply' (nextEl (rtransSpine L N r x i)) n
          (ytransSpine L N r x i)]
        exact hzn
      have hnext_r_d : nextEl r ((nextEl (rtransSpine L N r x i))^[n]
          (ytransSpine L N r x i)) = ztransSpine L N r x i := by
        calc nextEl r ((nextEl (rtransSpine L N r x i))^[n] (ytransSpine L N r x i))
            = nextEl r ((nextEl r)^[n] (ytransSpine L N r x i)) := by rw [hpow_n]
          _ = (nextEl r)^[n + 1] (ytransSpine L N r x i) := by
                rw [← Function.iterate_succ_apply' (nextEl r) n
                  (ytransSpine L N r x i)]
          _ = (nextEl (rtransSpine L N r x i))^[n + 1]
                (ytransSpine L N r x i) := by rw [hpow_s]
          _ = ztransSpine L N r x i := hzn
      have hyir : ytransSpine L N r x i ∈ r := pnxvwfs1Spine L hL hta hgn hunL hm i hf
      have hdr : (nextEl (rtransSpine L N r x i))^[n]
          (ytransSpine L N r x i) ∈ r := by
        have h := memPowerNextEl hyir n
        rw [← hpow_n] at h
        exact h
      have hrndr : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
      have e1 : prevEl (rtransSpine L N r x i) (ztransSpine L N r x i)
          = (nextEl (rtransSpine L N r x i))^[n] (ytransSpine L N r x i) := by
        rw [← hnext_ri_d]
        exact Kepler.Text.TameLp.prevEl_nextEl hrnd hmem_d
      have e2 : prevEl r (ztransSpine L N r x i)
          = (nextEl (rtransSpine L N r x i))^[n] (ytransSpine L N r x i) := by
        rw [← hnext_r_d]
        exact Kepler.Text.TameLp.prevEl_nextEl hrndr hdr
      rw [e1, e2]

/-! ## §2 prev_el_betwn_ztran_rtrans（KBWPBHQ.hl:1357-1406） -/

/-- **HOL `Kbwpbhq.prev_el_betwn_ztran_rtrans`**（KBWPBHQ.hl:1357-1406）塔层
i 形：`¬final(i) ∧ marked ∧ next_el f x = w ⇒ prev_el rᵢ (l'z(i)) ∈ rᵢ ∧
indexf w (prev_el …) rᵢ < indexf w (l'z(i)) rᵢ ∧
indexf w (l'y(i)) rᵢ ≤ indexf w (prev_el …) rᵢ`。
证（HOL 同构；详见文件头 ②）。 -/
theorem prevElBetwnZtranRtransSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    prevEl (rtransSpine L N r x i) (ztransSpine L N r x i)
        ∈ rtransSpine L N r x i
      ∧ indexf w (prevEl (rtransSpine L N r x i) (ztransSpine L N r x i))
          (rtransSpine L N r x i)
        < indexf w (ztransSpine L N r x i) (rtransSpine L N r x i)
      ∧ indexf w (ytransSpine L N r x i) (rtransSpine L N r x i)
        ≤ indexf w (prevEl (rtransSpine L N r x i) (ztransSpine L N r x i))
          (rtransSpine L N r x i) := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hyi : ytransSpine L N r x i ∈ rtransSpine L N r x i :=
    ytransMemRtrans L hL hgn hmr hf
  have hzi : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hf
  have hrnd : (rtransSpine L N r x i).Nodup :=
    (normalListUniqNonnil hmr.1.2.1 hmr.1.2.2.1).1
  have hwr : w ∈ rtransSpine L N r x i := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm i
  have hle := indexfYLeZInRSpine L hL hta hgn hm i hf hfind hw
  have hA := indexfAddLeft hwr hyi hzi (Nat.le_of_lt hle)
  have hpos : 0 < indexf (ytransSpine L N r x i) (ztransSpine L N r x i)
      (rtransSpine L N r x i) := by omega
  have hwzlt : indexf w (ztransSpine L N r x i) (rtransSpine L N r x i)
      < (rtransSpine L N r x i).length := indexfLtSizel hwr hzi
  obtain ⟨n, hn⟩ : ∃ n, indexf (ytransSpine L N r x i)
      (ztransSpine L N r x i) (rtransSpine L N r x i) = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hzn : (nextEl (rtransSpine L N r x i))^[n + 1]
      (ytransSpine L N r x i) = ztransSpine L N r x i := by
    rw [← hn]
    exact indexfN hyi hzi hrnd
  have hmem_d : (nextEl (rtransSpine L N r x i))^[n]
      (ytransSpine L N r x i) ∈ rtransSpine L N r x i := memPowerNextEl hyi n
  have hnext_ri_d : nextEl (rtransSpine L N r x i)
      ((nextEl (rtransSpine L N r x i))^[n] (ytransSpine L N r x i))
      = ztransSpine L N r x i := by
    rw [← Function.iterate_succ_apply' (nextEl (rtransSpine L N r x i)) n
      (ytransSpine L N r x i)]
    exact hzn
  have hpv : prevEl (rtransSpine L N r x i) (ztransSpine L N r x i)
      = (nextEl (rtransSpine L N r x i))^[n] (ytransSpine L N r x i) := by
    rw [← hnext_ri_d]
    exact Kepler.Text.TameLp.prevEl_nextEl hrnd hmem_d
  rw [hpv]
  -- indexf w d rᵢ = n + w→y
  have hwd : indexf w ((nextEl (rtransSpine L N r x i))^[n]
      (ytransSpine L N r x i)) (rtransSpine L N r x i)
      = n + indexf w (ytransSpine L N r x i) (rtransSpine L N r x i) := by
    refine nextElnIndexf hwr hmem_d hrnd ?_ (by omega)
    rw [Function.iterate_add_apply, indexfN hwr hyi hrnd]
  rw [hwd]
  refine ⟨hmem_d, ?_, ?_⟩ <;> omega

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.prevElConstZtranRtransSpine
#print axioms Kepler.Text.TameSpine.prevElBetwnZtranRtransSpine
