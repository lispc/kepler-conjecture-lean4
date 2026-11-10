/-
  Kepler.Text.TameSpine.Reduction3Kbwpbhq1 — tame-corr nb8：KBWPBHQ 章
  KBWPBHQ1 主件及其直接上游（波 B2）。

  ┌─ 归属对账（HOL → spine 形）───────────────────────────────────
  │ ① `nextElLyNeFListSpine`（KBWPBHQ1 证体 KBWPBHQ.hl:1142-1180 的
  │    内嵌段，单列为件）：marked ∧ ¬final r ⇒
  │    next_el r (l'y) ≠ f_list L (l'y)。证（HOL 同构）：¬final 取离面点
  │    x′（allPn 逆否）+ indexf_n[w;x′;r]（w = next_el r x）⟹
  │    indexf w x′ r ∈ {l'm 集} + MIN_LEAST（sInf 成员）+ l_y_rep_power。
  │ ② `nextElConstLeIndexfY0Spine`（KBWPBHQ.hl:441-488
  │    next_el_const_le_indexf_y0）：0 < transform_count ∧ d ∈ r ∧
  │    indexf w d r < indexf w (l'y(0)) r ⇒ next_el r d = f_list L d。
  │    证 = next_el_power_trans_eq_f@0 双实例（n := w→d r 与 n+1）+
  │    indexf_n（r 上）+ 同面 congr + fListPowEqNextElPow@1。
  │    （HOL 证体另引 indexf_next_el_le :360 与 indexf_const_le_indexf_ytrans；
  │    本件以 d 处的 fListPowEqNextElPow@1 收口、未消费这两步，故 :360
  │    未移植——本文件四件的证明均不需要它。）
  │ ③ `exsitsYtransLeCountSpine`（KBWPBHQ.hl:730-798
  │    EXSITS_YTRANS_LE_COUNT）：d ∈ r ∧ d ∈ f ∧ transform_count = t ∧
  │    ¬(next_el r d = f_list L d) ⇒ ∀ i, indexf w d f <
  │    indexf w (l'y(i)) f ∧ i < t ⇒ ∃ j, l'y(j) = d ∧ j < t。
  │    证（HOL 同构，对 i 归纳）：零支 indexf_const_le_f 双实例 + ② 反证；
  │    步支三分——< 支 IH；= 支 indexf_n×2；> 支再二分：CASES1 反证 /
  │    QCDVKEA + indexf_add_left×2 + next_el_const_betwn_ztran_ytrans_suc
  │    （nb7）反证。
  │ ④ `kbwpbhq1Spine`（KBWPBHQ.hl:1114-1242 **KBWPBHQ1**）：
  │    MEM u r ∧ MEM u (find_face L x) ⇒ ((∃ i, l'y(i) = u ∧
  │    i < transform_count) ⟺ ¬(next_el (find_list N u) u = f_list L u))。
  │    证（HOL 同构）：find_list_uniq 化 find_list N u = r；
  │    ⟹：transform_count_not + next_ytrans_const（波 B1）+ ①@塔层 i；
  │    ⟸：t = 0 支 final_list_transform_count + final_list 定义点态
  │    （HOL 经 final_list_power@1，同一事实）；t > 0 支对
  │    indexf w u f 与 indexf w (l'y(t−1)) f 三分——< 支 ③；= 支
  │    indexf_n×2；> 支二分 CASES1 / next_el_const_betwn_ztran_w_suc
  │    （波 A）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull，transformCountSpine /
  │ findListSpine）；消费件（aqiunpp3 / normalListUniqNonnil / lYRepPower
  │ / transformCountSpineNot / finalListTransformCountSpine /
  │ nextElPowerTransEqFSpine / nextMarkMemRTransSpine / indexfConstLeFSpine
  │ / pplhuljV0 / qcdvkeaTowerSpine / cases1 /
  │ nextElConstBetwnZtranYtransSucSpine / nextElConstBetwnZtranWSucSpine /
  │ nextYtransConstSpine / findListUniq / fListPowEqNextElPow /
  │ aq10_memNextMarkInface / TameList3 indexf 族 / memPowerNextEl /
  │ TameLp 面件）同世界零混合；零 Dart 载体件。默认心跳、linter 全开。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqCases2
import Kepler.Text.TameSpine.Reduction3KbwpbhqYtransConst

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup findFaceDarts_congr_of_mem
  nextEl_mem_of_mem)

/-! ## §1 l'y 离面性质（KBWPBHQ.hl:1142-1180 内嵌段） -/

/-- **l'y 离面性质**（HOL KBWPBHQ1 证体 KBWPBHQ.hl:1142-1180 的内嵌段）：
`marked_list ∧ ¬final_list L r ⇒ next_el r (l'y) ≠ f_list L (l'y)`。
证（HOL 同构）：¬final 取离面点 x′；indexf_n[w;x′;r]（w = next_el r x）
给 indexf w x′ r 落在 l'm 的定义集内；sInf 成员（HOL Nuxcoea.MIN_LEAST）
给 l'm 自身落在集内；l_y_rep_power 换回 l'y。 -/
theorem nextElLyNeFListSpine (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬ finalListSpine L r) :
    nextEl r (lYSpine L r x) ≠ fList L (lYSpine L r x) := by
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hex : ∃ x' ∈ r, fList L x' ≠ nextEl r x' := by
    by_contra hall
    apply hf
    intro d hd
    by_contra hne
    exact hall ⟨d, hd, hne⟩
  obtain ⟨x', hx'r, hx'ne⟩ := hex
  have hwr : nextEl r x ∈ r := nextEl_mem_of_mem hxr
  have hpow : (nextEl r)^[indexf (nextEl r x) x' r] (nextEl r x) = x' :=
    indexfN hwr hx'r hrnd
  have e1 : (nextEl r)^[indexf (nextEl r x) x' r + 1] x = x' := by
    rw [Function.iterate_succ_apply]
    exact hpow
  have e2 : (nextEl r)^[indexf (nextEl r x) x' r + 2] x = nextEl r x' := by
    rw [Function.iterate_succ_apply', e1]
  have hmem : indexf (nextEl r x) x' r
      ∈ {m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)} := by
    show (nextEl r)^[indexf (nextEl r x) x' r + 2] x
      ≠ fList L ((nextEl r)^[indexf (nextEl r x) x' r + 1] x)
    rw [e1, e2]
    exact fun h => hx'ne h.symm
  have hlm : lMSpine L r x
      ∈ {m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)} :=
    Nat.sInf_mem ⟨_, hmem⟩
  have h2 : (nextEl r)^[lMSpine L r x + 2] x
      ≠ fList L ((nextEl r)^[lMSpine L r x + 1] x) := hlm
  rw [Function.iterate_succ_apply' (nextEl r) (lMSpine L r x + 1) x] at h2
  rw [lYRepPower L r x hnext.symm]
  exact h2

/-! ## §2 next_el_const_le_indexf_y0（KBWPBHQ.hl:441-488） -/

/-- **HOL `Kbwpbhq.next_el_const_le_indexf_y0`**（KBWPBHQ.hl:441-488）：
`0 < transform_count ∧ d ∈ r ∧ indexf w d r < indexf w (l'y(0)) r ⇒
next_el r d = f_list L d`。
证 = next_el_power_trans_eq_f@0 双实例（n := w→d r 与 n+1，界由前提）+
indexf_n（r 上）+ 同面等表 congr + fListPowEqNextElPow@1。 -/
theorem nextElConstLeIndexfY0Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (ht0 : 0 < transformCountSpine L N r x)
    {d : ℕ × ℕ} (hd : d ∈ r)
    (hlt : indexf w d r < indexf w (ytransSpine L N r x 0) r) :
    nextEl r d = fList L d := by
  have hf0 : ¬ finalListSpine L (rtransSpine L N r x 0) :=
    transformCountSpineNot L N r x ht0
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hwr : w ∈ r := by
    have h := nextMarkMemRTransSpine L hL hgn hta hm 0
    rw [show rtransSpine L N r x 0 = r from rfl, hfind, hw] at h
    exact h
  have hdn : (nextEl r)^[indexf w d r] w = d := indexfN hwr hd hrnd
  have hb1 : indexf w d r ≤ indexf w (ytransSpine L N r x 0) r :=
    Nat.le_of_lt hlt
  have hb2 : indexf w d r + 1 ≤ indexf w (ytransSpine L N r x 0) r := hlt
  have hp1 := nextElPowerTransEqFSpine L hL hta hgn hm 0 hf0 hfind hw
    (n := indexf w d r) hb1
  have hp2 := nextElPowerTransEqFSpine L hL hta hgn hm 0 hf0 hfind hw
    (n := indexf w d r + 1) hb2
  rw [show rtransSpine L N r x 0 = r from rfl, hfind] at hp1 hp2
  rw [hdn] at hp1
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hdn,
    ← hp1] at hp2
  -- d ∈ f，f_list L d = next_el f d
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hdf : d ∈ f := by
    rw [hp1]
    exact memPowerNextEl hwf _
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hdfx : d ∈ findFaceDarts L x := by
    rw [hfind]
    exact hdf
  have hcong : findFaceDarts L d = f :=
    (findFaceDarts_congr_of_mem hL.1 hxd hdfx).trans hfind
  have hdd : d ∈ findFaceDarts L d := by
    rw [hcong]
    exact hdf
  have hfl := fListPowEqNextElPow L hL d hdd 1
  simp only [Function.iterate_one] at hfl
  rw [hcong] at hfl
  rw [hp2, hfl]

/-! ## §3 EXSITS_YTRANS_LE_COUNT（KBWPBHQ.hl:730-798） -/

/-- **HOL `Kbwpbhq.EXSITS_YTRANS_LE_COUNT`**（KBWPBHQ.hl:730-798）：
`MEM d r ∧ MEM d f ∧ transform_count = t ∧ ¬(next_el r d = f_list L d) ⇒
∀ i, indexf w d f < indexf w (l'y(i)) f ∧ i < t ⇒ ∃ j, l'y(j) = d ∧ j < t`。
证（HOL 同构，对 i 归纳；详见文件头 ③）。 -/
theorem exsitsYtransLeCountSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {t : ℕ} (ht : transformCountSpine L N r x = t)
    {d : ℕ × ℕ} (hdr : d ∈ r) (hdf : d ∈ f)
    (hne : ¬ (nextEl r d = fList L d)) :
    ∀ i, indexf w d f < indexf w (ytransSpine L N r x i) f ∧ i < t →
      ∃ j, ytransSpine L N r x j = d ∧ j < t := by
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  intro i
  induction i with
  | zero =>
    rintro ⟨h1, h2⟩
    exfalso
    have hf0 : ¬ finalListSpine L (rtransSpine L N r x 0) :=
      transformCountSpineNot L N r x (by omega)
    have hCd := indexfConstLeFSpine L hL hta hgn hm 0 hf0 hfind hw hdf
      (Nat.le_of_lt h1)
    have hf0r : ¬ finalListSpine L r := hf0
    obtain ⟨hyf0, -, -⟩ := pplhuljV0 L hL hgn hunL hm hf0r
    rw [hfind] at hyf0
    have hy0f : ytransSpine L N r x 0 ∈ f := hyf0
    have hCy := indexfConstLeFSpine L hL hta hgn hm 0 hf0 hfind hw hy0f
      (le_refl _)
    rw [show rtransSpine L N r x 0 = r from rfl] at hCd hCy
    exact hne (nextElConstLeIndexfY0Spine L hL hta hgn hm hfind hw (by omega)
      hdr (by omega))
  | succ i ih =>
    rintro ⟨h1, h2⟩
    have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
      transformCountSpineNot L N r x (by omega)
    have hfs : ¬ finalListSpine L (rtransSpine L N r x (i + 1)) :=
      transformCountSpineNot L N r x (by omega)
    have hmr := aqiunpp3 L hL i hta hgn hm
    obtain ⟨hyf0, hzf0, -⟩ := pplhuljV0 L hL hgn hunL hmr hfi
    rw [hfind] at hyf0 hzf0
    have hyif : ytransSpine L N r x i ∈ f := hyf0
    have hzif : ztransSpine L N r x i ∈ f := hzf0
    rcases lt_trichotomy (indexf w d f)
      (indexf w (ytransSpine L N r x i) f) with hlt | heq | hgt
    · exact ih ⟨hlt, by omega⟩
    · refine ⟨i, ?_, by omega⟩
      have e1 := indexfN hwf hdf hfnd
      have e2 := indexfN hwf hyif hfnd
      rw [← heq] at e2
      exact e2.symm.trans e1
    · exfalso
      have hQ := qcdvkeaTowerSpine L hL hta hgn hm i hfs hfind hw
      by_cases hc : indexf w d f < indexf w (ztransSpine L N r x i) f
      · exact cases1 L hL hta hgn hunL hm hfind hw hfi hc hgt hdf hdr
      · have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
        obtain ⟨hysf0, -, -⟩ := pplhuljV0 L hL hgn hunL hmr1 hfs
        rw [hfind] at hysf0
        have hysf : ytransSpine L N r x (i + 1) ∈ f := hysf0
        have hA1 := indexfAddLeft hwf hzif hdf (by omega)
        have hA2 := indexfAddLeft hwf hzif hysf hQ
        exact hne (nextElConstBetwnZtranYtransSucSpine L hL hta hgn hunL hm i
          hfs hfind hw hdf (by omega))

/-! ## §4 KBWPBHQ1（KBWPBHQ.hl:1114-1242） -/

/-- **HOL `Kbwpbhq.KBWPBHQ1`**（KBWPBHQ.hl:1114-1242）：
`MEM u r ∧ MEM u (find_face L x) ⇒ ((∃ i, l'y(i) = u ∧
i < transform_count L N r x) ⟺ ¬(next_el (find_list N u) u = f_list L u))`。
证（HOL 同构；详见文件头 ④）。 -/
theorem kbwpbhq1Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {u : ℕ × ℕ} (hur : u ∈ r) (huf : u ∈ findFaceDarts L x) :
    (∃ i, ytransSpine L N r x i = u ∧ i < transformCountSpine L N r x)
      ↔ ¬ (nextEl (findListSpine N u) u = fList L u) := by
  have hfl : findListSpine N u = r := findListUniq hm.1.2.1.1 hur hm.1.2.2.1
  rw [hfl]
  obtain ⟨t, ht⟩ : ∃ t, transformCountSpine L N r x = t := ⟨_, rfl⟩
  rw [ht]
  obtain ⟨w, hw⟩ : ∃ w, nextEl (findFaceDarts L x) x = w := ⟨_, rfl⟩
  constructor
  · -- ⟹：next_ytrans_const + l'y 离面性质
    rintro ⟨i, hyu, hit⟩ hcon
    have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
      transformCountSpineNot L N r x (by omega)
    have hmr := aqiunpp3 L hL i hta hgn hm
    have hconst := nextYtransConstSpine L hL hta hgn hunL hm i hfi
    apply nextElLyNeFListSpine L hL hmr hfi
    show nextEl (rtransSpine L N r x i) (ytransSpine L N r x i)
      = fList L (ytransSpine L N r x i)
    rw [hconst, hyu]
    exact hcon
  · -- ⟸
    intro hne
    by_contra hnex
    rcases Nat.eq_zero_or_pos t with ht0 | ht0
    · -- t = 0：final r ⟹ f_list L u = next_el r u
      have hfin := finalListTransformCountSpine L hL hta hgn hm ht
      rw [ht0, show rtransSpine L N r x 0 = r from rfl] at hfin
      exact hne (hfin u hur).symm
    · have hfi : ¬ finalListSpine L (rtransSpine L N r x (t - 1)) :=
        transformCountSpineNot L N r x (by omega)
      have hmr := aqiunpp3 L hL (t - 1) hta hgn hm
      have hwf : w ∈ findFaceDarts L x := by
        rw [← hw]
        exact aq10_memNextMarkInface L hL hgn hm
      have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
      obtain ⟨hyf0, -, -⟩ := pplhuljV0 L hL hgn hunL hmr hfi
      have hyif : ytransSpine L N r x (t - 1) ∈ findFaceDarts L x := hyf0
      rcases lt_trichotomy (indexf w u (findFaceDarts L x))
        (indexf w (ytransSpine L N r x (t - 1)) (findFaceDarts L x))
        with hlt | heq | hgt
      · exact hnex (exsitsYtransLeCountSpine L hL hta hgn hunL hm rfl hw ht
          hur huf hne (t - 1) ⟨hlt, by omega⟩)
      · apply hnex
        refine ⟨t - 1, ?_, by omega⟩
        have e1 := indexfN hwf huf hfnd
        have e2 := indexfN hwf hyif hfnd
        rw [← heq] at e2
        exact e2.symm.trans e1
      · by_cases hc : indexf w u (findFaceDarts L x)
            < indexf w (ztransSpine L N r x (t - 1)) (findFaceDarts L x)
        · exact cases1 L hL hta hgn hunL hm rfl hw hfi hc hgt huf hur
        · exact hne (nextElConstBetwnZtranWSucSpine L hL hta hgn hunL hm rfl hw
            ht0 ht huf (by omega))

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.nextElLyNeFListSpine
#print axioms Kepler.Text.TameSpine.nextElConstLeIndexfY0Spine
#print axioms Kepler.Text.TameSpine.exsitsYtransLeCountSpine
#print axioms Kepler.Text.TameSpine.kbwpbhq1Spine
