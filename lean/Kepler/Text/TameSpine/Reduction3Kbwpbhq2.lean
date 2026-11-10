/-
  Kepler.Text.TameSpine.Reduction3Kbwpbhq2 — tame-corr nb9：KBWPBHQ 章
  **KBWPBHQ2**（prev_el 侧主件，KBWPBHQ :1794–:2003）。

  ┌─ 归属对账（HOL → spine 形）───────────────────────────────────
  │ `kbwpbhq2Spine`（HOL `Kbwpbhq.KBWPBHQ2`）：
  │ `MEM u r ∧ MEM u (find_face L x) ⇒
  │  ((∃ i, l'z(i) = u ∧ i < transform_count) ⟺
  │   ¬(f_list L (prev_el (find_list N u) u) = u))`。
  │ 证（HOL 同构，两支）：
  │ ⟹：给定 i、l'z(i) = u、i < t（⟹ ¬final(i)）：
  │    prev_el_const_ztran_rtrans（nb9 件 2）⟹ prev_el rᵢ u = prev_el r u（P）；
  │    反设 f_list L P = u。prev_not_in_suc_or_ytrans（件 5）二分：
  │    · P ∉ r(i+1)：prevElBetwnZtranYtransOnF（件 4）+ prev_mem_r_suc（件 6）
  │      给 prev_el f u ∈ r(i+1)；由 prev_fList_inverse（TameLp:5127）与
  │      面 congr 得 prev_el f u = P，与 P ∉ r(i+1) 相抵。
  │    · P = l'y(i)：nextEl_prevEl（TameLp:4954）给 next_el rᵢ l'y(i) = u，
  │      与反设合取即 next_el rᵢ l'y(i) = f_list L l'y(i)，与
  │      l'y 离面性质（nb8 nextElLyNeFListSpine @塔层 i）相抵。
  │ ⟸：给定 ¬(f_list L P = u)，t = transform_count：
  │    · t = 0 支：final r ⟹ 每个元素 f_list = next_el，且
  │      next_el r (prev_el r u) = u（prevEl_nextEl），与 hne 相抵
  │      （HOL 经 final_list_power@1 绕行，同一事实；本件用 final_list 定义点态）。
  │    · t > 0 支：i := t−1，先分 w→u f = 0 / > 0——= 0 支 w = u
  │      （indexfZeroEq）⟹ next_el r x = u（marked 的 next_el = f_list 合取）
  │      ⟹ prev_el r u = x（prevEl_nextEl）⟹ f_list L x = u ⟹ 与 hne 相抵；
  │      > 0 支对 w→u 与 w→l'y(i) 三分——< 支 EXSITS_ZTRANS_LE_COUNT（件 10）；
  │      = 支 indexf_n×2 取 j := i；> 支再对 w→u 与 w→l'z(i) 三分——
  │      < 支 CASES1 反证（u ∈ r）、= 支 indexf_n×2 取 j := i、
  │      > 支 prev_el_const_betwn_ztran_w_suc（件 11）与 hne 相抵。
  │ 查重：`find_list N u = r` 由 findListUniq（TameList9:582）；prev 侧
  │ 引擎件见 nb9 件 2/4/5/6/10/11；链世界同题件按名零命中（本笔为
  │ spine 世界首落）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（findListUniq /
  │ transformCountSpineNot / aqiunpp3 / memZtransRtransSpine /
  │ prevElConstZtranRtransSpine / prevElBetwnZtranRtransSpine /
  │ prevElBetwnZtranYtransOnFSpine / prevNotInSucOrYtransSpine /
  │ prevMemRSucSpine / exsitsZtransLeCountSpine /
  │ prevElConstBetwnZtranWSucSpine（均 nb9）/ nextElLyNeFListSpine（nb8）/
  │ finalListTransformCountSpine / pplhuljV0 / qcdvkeaTowerSpine / cases1 /
  │ prev_fList_inverse / prevEl_nextEl / nextEl_prevEl /
  │ prevEl_mem_of_mem / findFaceDarts_congr_of_mem / normalListListOfDarts /
  │ TameList3 indexf 族）。BEq 世界：nextEl/prevEl 全走环境实例 +
  │ TameLp 的 nextEl_prevEl/prevEl_nextEl 桥（见 nb9 件 2 头注）。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqPrev3
import Kepler.Text.TameSpine.Reduction3Kbwpbhq1

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts prevEl)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup findFaceDarts_congr_of_mem)

/-- **HOL `Kbwpbhq.KBWPBHQ2`**（KBWPBHQ.hl:1794-2003）：
`MEM u r ∧ MEM u (find_face L x) ⇒ ((∃ i, l'z(i) = u ∧
i < transform_count L N r x) ⟺ ¬(f_list L (prev_el (find_list N u) u) = u))`。
证（HOL 同构；详见文件头）。 -/
theorem kbwpbhq2Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {u : ℕ × ℕ} (hur : u ∈ r) (huf : u ∈ findFaceDarts L x) :
    (∃ i, ztransSpine L N r x i = u ∧ i < transformCountSpine L N r x)
      ↔ ¬ (fList L (prevEl (findListSpine N u) u) = u) := by
  have hfl : findListSpine N u = r := findListUniq hm.1.2.1.1 hur hm.1.2.2.1
  rw [hfl]
  obtain ⟨t, ht⟩ : ∃ t, transformCountSpine L N r x = t := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, nextEl (findFaceDarts L x) x = w := ⟨_, rfl⟩
  have hwf : w ∈ findFaceDarts L x := by
    rw [← hw]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  constructor
  · -- ⟹
    rintro ⟨i, hzi, hit⟩ hcon
    rw [← hzi] at hcon
    have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
      transformCountSpineNot L N r x (by omega)
    have hmr := aqiunpp3 L hL i hta hgn hm
    have hP := prevElConstZtranRtransSpine L hL hta hgn hunL hm i hfi rfl hw
    have hPri : prevEl (rtransSpine L N r x i) (ztransSpine L N r x i)
        ∈ rtransSpine L N r x i :=
      (prevElBetwnZtranRtransSpine L hL hta hgn hunL hm i hfi rfl hw).1
    have hPdarts : prevEl (rtransSpine L N r x i) (ztransSpine L N r x i)
        ∈ listOfDarts L :=
      normalListListOfDarts hmr.1.2.1 _
        (List.mem_flatten.mpr ⟨rtransSpine L N r x i, hmr.1.2.2.1, hPri⟩)
    have hFsuc : prevEl (findFaceDarts L x) (ztransSpine L N r x i)
        ∈ rtransSpine L N r x (i + 1) :=
      prevMemRSucSpine L hL hta hgn hunL hm i hfi rfl hw
    rcases prevNotInSucOrYtransSpine L hL hta hgn hunL hm i hfi rfl hw
      with hcaseA | hcaseB
    · -- P ∉ r(i+1)：prev_el f u = P 与之相抵
      have hpv := Kepler.Text.TameLp.prev_fList_inverse hL.1 hPdarts
      rw [← hP] at hcon
      rw [hcon] at hpv
      obtain ⟨-, hzf0, -⟩ := pplhuljV0 L hL hgn hunL hmr hfi
      have hcongz : findFaceDarts L (ztransSpine L N r x i) = findFaceDarts L x :=
        findFaceDarts_congr_of_mem hL.1 hxd hzf0
      rw [hcongz] at hpv
      rw [hpv] at hFsuc
      exact hcaseA hFsuc
    · -- P = l'y(i)：与 l'y 离面性质相抵
      have hzim : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
        memZtransRtransSpine L hL hgn hunL hta hm i hfi
      have hrind : (rtransSpine L N r x i).Nodup :=
        (normalListUniqNonnil hmr.1.2.1 hmr.1.2.2.1).1
      have hnextri : nextEl (rtransSpine L N r x i)
          (prevEl (rtransSpine L N r x i) (ztransSpine L N r x i))
          = ztransSpine L N r x i :=
        Kepler.Text.TameLp.nextEl_prevEl (s := rtransSpine L N r x i) hrind hzim
      rw [hcaseB] at hnextri
      rw [← hP] at hcon
      rw [hcaseB] at hcon
      apply nextElLyNeFListSpine L hL hmr hfi
      show nextEl (rtransSpine L N r x i) (ytransSpine L N r x i)
        = fList L (ytransSpine L N r x i)
      rw [hcon, hnextri]
  · -- ⟸
    intro hne
    by_contra hnex
    rw [ht] at hnex
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · -- t = 0：final r
      exfalso
      have hfin := finalListTransformCountSpine L hL hta hgn hm ht
      rw [ht0, show rtransSpine L N r x 0 = r from rfl] at hfin
      have hpr : prevEl r u ∈ r := Kepler.Text.TameLp.prevEl_mem_of_mem hur
      have hnext : nextEl r (prevEl r u) = u :=
        Kepler.Text.TameLp.nextEl_prevEl hrnd hur
      have hfl' := hfin (prevEl r u) hpr
      exact hne (by rw [hfl', hnext])
    · have hfi : ¬ finalListSpine L (rtransSpine L N r x (t - 1)) :=
        transformCountSpineNot L N r x (by omega)
      have hmr := aqiunpp3 L hL (t - 1) hta hgn hm
      obtain ⟨hyf0, hzf0, hlt0⟩ := pplhuljV0 L hL hgn hunL hmr hfi
      rw [hw] at hlt0
      have hyif : ytransSpine L N r x (t - 1) ∈ findFaceDarts L x := hyf0
      have hzif : ztransSpine L N r x (t - 1) ∈ findFaceDarts L x := hzf0
      have hlt : indexf w (ytransSpine L N r x (t - 1)) (findFaceDarts L x)
          < indexf w (ztransSpine L N r x (t - 1)) (findFaceDarts L x) := hlt0
      rcases Nat.eq_zero_or_pos (indexf w u (findFaceDarts L x)) with h0 | hpos
      · -- w→u = 0：w = u ⟹ prev_el r u = x 与 hne 相抵
        exfalso
        have hwu : w = u := indexfZeroEq hwf huf h0
        have hxu : nextEl (findFaceDarts L x) x = u := by
          rw [hw]
          exact hwu
        have hfx : fList L x = u := hxu
        have hxnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
        have hxr : x ∈ r := hm.1.2.2.2.1
        have hu2 : nextEl r x = u := by rw [hxnext]; exact hfx
        have hpr : prevEl r u = x := by
          rw [← hu2]
          exact Kepler.Text.TameLp.prevEl_nextEl hrnd hxr
        exact hne (by rw [hpr, hfx])
      · rcases Nat.lt_or_ge (indexf w (ytransSpine L N r x (t - 1)) (findFaceDarts L x))
          (indexf w u (findFaceDarts L x)) with hyu_lt | hle1
        · -- w→y < w→u：对 w→u 与 w→z 三分
          rcases lt_trichotomy (indexf w u (findFaceDarts L x))
            (indexf w (ztransSpine L N r x (t - 1)) (findFaceDarts L x))
            with hlt2 | heq2 | hgt2
          · exact absurd hur (cases1 L hL hta hgn hunL hm rfl hw hfi hlt2 hyu_lt huf)
          · apply hnex
            refine ⟨t - 1, ?_, by omega⟩
            have e1 := indexfN hwf hzif hfnd
            have e2 := indexfN hwf huf hfnd
            rw [heq2] at e2
            exact e1.symm.trans e2
          · exact hne (prevElConstBetwnZtranWSucSpine L hL hta hgn hunL hm
              rfl hw ht0 ht huf hgt2)
        · -- w→u ≤ w→y：EXSITS_ZTRANS_LE_COUNT
          exact hnex (exsitsZtransLeCountSpine L hL hta hgn hunL hm rfl hw ht
            hur huf hne (t - 1) ⟨hpos, hle1, by omega⟩)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.kbwpbhq2Spine
