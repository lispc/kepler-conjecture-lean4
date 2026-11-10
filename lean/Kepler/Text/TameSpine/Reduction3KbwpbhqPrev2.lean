/-
  Kepler.Text.TameSpine.Reduction3KbwpbhqPrev2 — tame-corr nb9：KBWPBHQ 章
  prev_el 侧第 4–6 件（KBWPBHQ :1409–:1552）。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ ① `prevElBetwnZtranYtransOnFSpine`（KBWPBHQ.hl:1409-1465
  │    prev_el_betwn_ztran_ytrans_on_f，**在 f 上**）：¬final(i) ∧ marked
  │    ∧ next_el f x = w ⇒ prev_el f (l'z(i)) ∈ f ∧
  │    indexf w (prev_el …) f < indexf w (l'z(i)) f ∧
  │    (indexf w (l'y(i)) f < indexf w (prev_el …) f ∨ prev_el f (l'z(i)) = l'y(i))。
  │    证（HOL 同构）：PPLHULJ（0 < w→z）+ n := PRE (w→z)、d := (next_el f)^n w
  │    + indexf_n 给 next_el f d = z + prevEl_nextEl 得 prev_el f z = d；
  │    next_eln_indexf 给 indexf w d f = n；合取 3 对 n 与 w→y 二分
  │    （HOL 用三支改写，本件用「w→y < w→z = n+1」一次收口：w→y < n 支
  │    直接左；w→y = n 支 indexf_n 给 d = y）。
  │ ② `prevNotInSucOrYtransSpine`（KBWPBHQ.hl:1471-1524
  │    prev_not_in_suc_or_ytrans）：¬final(i) ∧ marked ∧ w ⇒
  │    prev_el rᵢ (l'z(i)) ∉ r(i+1) ∨ prev_el rᵢ (l'z(i)) = l'y(i)。
  │    证（HOL 同构）：prev_el_betwn_ztran_rtrans（nb9 件 2）三合取 +
  │    PWSSRAT（d ∈ r(i+1) ⟺ z→d ≤ z→y）+ indexf_add_left×3 +
  │    indexf_antisym×2——y = z 支与 z ≠ y 相抵、d = z 支与 w→d < w→z 相抵、
  │    主支按 z→y < z→d（⟹ ¬MEM，PWSSRAT 逆否）/ =（indexf_n×2 ⟹ d = y）二分。
  │ ③ `prevMemRSucSpine`（KBWPBHQ.hl:1528-1552 prev_mem_r_suc）：
  │    ¬final(i) ∧ marked ∧ w ⇒ prev_el f (l'z(i)) ∈ r(i+1)。
  │    证（HOL 同构）：① 三合取 + indexf_n[w;d;f] + NCVIBWU 塔层形
  │    @j:=w→d f（界 = ① 合取 2）。
  │ 查重记档：`change_f_list_prev_el`（:1554）在库 = `changeFListPrevEl`
  │ （Reduction5Qcdvkea:52，陈述逐字，本文件不重落；需要时经
  │ `Kepler.Text.TameLp.prev_fList_inverse` 直投）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ pplhuljV0 / aq10_memNextMarkInface / indexfN / nextElnIndexf /
  │ indexfLtSizel / memPowerNextEl / prevEl_nextEl（TameLp:4921）/
  │ prevElBetwnZtranRtransSpine（nb9）/ hqymrtx3List / pwssratSpine
  │ （nb5）/ ncvibwuTowerSpine（nb2）/ indexfAntisym / indexfAddLeft /
  │ indexfAddRight / findFaceDarts_nodup / TameLp 面件）同世界零混合；
  │ BEq 世界：nextEl 全走环境实例（instBEqProd，与塔族一致），prevEl
  │ 走 instBEqOfDecidableEq——两世界只在 `prevEl (nextEl _)` 处相交，
  │ 经 prevEl_nextEl 桥（其 nextEl 吃环境实例）接通。零 Dart 载体件。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqPrev

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts prevEl)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup)

/-! ## §1 prev_el_betwn_ztran_ytrans_on_f（KBWPBHQ.hl:1409-1465） -/

/-- **HOL `Kbwpbhq.prev_el_betwn_ztran_ytrans_on_f`**（KBWPBHQ.hl:1409-1465）
塔层 i 形（在 f 上）：`¬final(i) ∧ marked ∧ next_el f x = w ⇒
prev_el f (l'z(i)) ∈ f ∧ indexf w (prev_el …) f < indexf w (l'z(i)) f ∧
(indexf w (l'y(i)) f < indexf w (prev_el …) f ∨
  prev_el f (l'z(i)) = l'y(i))`。证（HOL 同构；详见文件头 ①）。 -/
theorem prevElBetwnZtranYtransOnFSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    prevEl f (ztransSpine L N r x i) ∈ f
      ∧ indexf w (prevEl f (ztransSpine L N r x i)) f
          < indexf w (ztransSpine L N r x i) f
      ∧ (indexf w (ytransSpine L N r x i) f
            < indexf w (prevEl f (ztransSpine L N r x i)) f
          ∨ prevEl f (ztransSpine L N r x i) = ytransSpine L N r x i) := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  obtain ⟨hyf0, hzf0, hlt0⟩ := pplhuljV0 L hL hgn hunL hmr hf
  rw [hfind] at hyf0 hzf0 hlt0
  rw [hw] at hlt0
  have hyff : ytransSpine L N r x i ∈ f := hyf0
  have hzif : ztransSpine L N r x i ∈ f := hzf0
  have hlt : indexf w (ytransSpine L N r x i) f
      < indexf w (ztransSpine L N r x i) f := hlt0
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  have hpos : 0 < indexf w (ztransSpine L N r x i) f := by omega
  obtain ⟨n, hn⟩ : ∃ n, indexf w (ztransSpine L N r x i) f = n + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hzn : (nextEl f)^[n + 1] w = ztransSpine L N r x i := by
    rw [← hn]
    exact indexfN hwf hzif hfnd
  have hmem_d : (nextEl f)^[n] w ∈ f := memPowerNextEl hwf n
  have hnext_d : nextEl f ((nextEl f)^[n] w) = ztransSpine L N r x i := by
    rw [← Function.iterate_succ_apply' (nextEl f) n w]
    exact hzn
  have hpv : prevEl f (ztransSpine L N r x i) = (nextEl f)^[n] w := by
    rw [← hnext_d]
    exact Kepler.Text.TameLp.prevEl_nextEl hfnd hmem_d
  rw [hpv]
  have hzlt : indexf w (ztransSpine L N r x i) f < f.length :=
    indexfLtSizel hwf hzif
  have hwd : indexf w ((nextEl f)^[n] w) f = n := by
    refine nextElnIndexf hwf hmem_d hfnd rfl (by omega)
  refine ⟨hmem_d, by omega, ?_⟩
  by_cases hc : indexf w (ytransSpine L N r x i) f < n
  · left
    omega
  · right
    have heq : indexf w (ytransSpine L N r x i) f = n := by omega
    have e1 := indexfN hwf hyff hfnd
    rw [heq] at e1
    exact e1

/-! ## §2 prev_not_in_suc_or_ytrans（KBWPBHQ.hl:1471-1524） -/

/-- **HOL `Kbwpbhq.prev_not_in_suc_or_ytrans`**（KBWPBHQ.hl:1471-1524）塔层
i 形：`¬final(i) ∧ marked ∧ w ⇒ prev_el rᵢ (l'z(i)) ∉ r(i+1) ∨
prev_el rᵢ (l'z(i)) = l'y(i)`。证（HOL 同构；详见文件头 ②）。 -/
theorem prevNotInSucOrYtransSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    prevEl (rtransSpine L N r x i) (ztransSpine L N r x i)
        ∉ rtransSpine L N r x (i + 1)
      ∨ prevEl (rtransSpine L N r x i) (ztransSpine L N r x i)
          = ytransSpine L N r x i := by
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
  obtain ⟨hdri, hlt1, hle1⟩ :=
    prevElBetwnZtranRtransSpine L hL hta hgn hunL hm i hf hfind hw
  -- 界：w→y + y→d = w→d、w→y + y→z = w→z、y→d + d→z = y→z
  have hA1 := indexfAddLeft hwr hyi hzi (by omega)
  have hA2 := indexfAddLeft hwr hyi hdri (by omega)
  have hA3 := indexfAddLeft hyi hdri hzi (by omega)
  -- d→z ≤ y→z（hA3 直出）
  have hdze : indexf (prevEl (rtransSpine L N r x i) (ztransSpine L N r x i))
      (ztransSpine L N r x i) (rtransSpine L N r x i)
      ≤ indexf (ytransSpine L N r x i) (ztransSpine L N r x i)
        (rtransSpine L N r x i) := by omega
  have hfeq := pwssratSpine L hL hta hgn hm i hdri hf
  by_cases hyz : ytransSpine L N r x i = ztransSpine L N r x i
  · exact absurd hyz (hqymrtx3List L hL hgn hunL hmr hf)
  by_cases hdz : prevEl (rtransSpine L N r x i) (ztransSpine L N r x i)
      = ztransSpine L N r x i
  · exfalso
    have hh : indexf w (prevEl (rtransSpine L N r x i) (ztransSpine L N r x i))
        (rtransSpine L N r x i)
        = indexf w (ztransSpine L N r x i) (rtransSpine L N r x i) := by rw [hdz]
    omega
  · have hanti1 := indexfAntisym hyi hzi hyz
    have hanti2 := indexfAntisym hdri hzi hdz
    by_cases hcase : indexf (ztransSpine L N r x i) (ytransSpine L N r x i)
        (rtransSpine L N r x i)
        < indexf (ztransSpine L N r x i)
          (prevEl (rtransSpine L N r x i) (ztransSpine L N r x i))
          (rtransSpine L N r x i)
    · left
      intro hmem
      rw [hfeq] at hmem
      omega
    · right
      have heq : indexf (ztransSpine L N r x i)
          (prevEl (rtransSpine L N r x i) (ztransSpine L N r x i))
          (rtransSpine L N r x i)
          = indexf (ztransSpine L N r x i) (ytransSpine L N r x i)
            (rtransSpine L N r x i) := by omega
      have e1 := indexfN hzi hyi hrnd
      have e2 := indexfN hzi hdri hrnd
      rw [heq] at e2
      exact e2.symm.trans e1

/-! ## §3 prev_mem_r_suc（KBWPBHQ.hl:1528-1552） -/

/-- **HOL `Kbwpbhq.prev_mem_r_suc`**（KBWPBHQ.hl:1528-1552）塔层 i 形：
`¬final(i) ∧ marked ∧ w ⇒ prev_el f (l'z(i)) ∈ r(i+1)`。
证（HOL 同构）：上件 ① 三合取 + indexf_n + NCVIBWU 塔层形 @j:=w→d f。 -/
theorem prevMemRSucSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    prevEl f (ztransSpine L N r x i) ∈ rtransSpine L N r x (i + 1) := by
  obtain ⟨hdf, hlt, -⟩ :=
    prevElBetwnZtranYtransOnFSpine L hL hta hgn hunL hm i hf hfind hw
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  obtain ⟨hmem, -⟩ :=
    ncvibwuTowerSpine L hL hta hgn hm i hf hfind hw
      (j := indexf w (prevEl f (ztransSpine L N r x i)) f) (Nat.le_of_lt hlt)
  rw [indexfN hwf hdf hfnd] at hmem
  exact hmem

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.prevElBetwnZtranYtransOnFSpine
#print axioms Kepler.Text.TameSpine.prevNotInSucOrYtransSpine
#print axioms Kepler.Text.TameSpine.prevMemRSucSpine
