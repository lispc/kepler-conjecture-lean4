/-
  Kepler.Text.TameSpine.Reduction3KbwpbhqPrev3 — tame-corr nb9：KBWPBHQ 章
  prev_el 侧第 8–11 件（KBWPBHQ :1569–:1789）。

  ┌─ 归属对账（HOL → spine 形）───────────────────────────────────
  │ ① `prevElConstLeIndexfY0Spine`（KBWPBHQ.hl:1569-1616
  │    prev_el_const_le_indexf_y0）：marked ∧ d ∈ f ∧ 0 < w→d f ∧
  │    w→d f ≤ w→l'y(0) f ∧ 0 < transform_count ⇒ f_list L (prev_el r d) = d。
  │    证（HOL 同构）：transform_count_not@0（¬final r）+ indexf_const_le_f
  │    双实例（d / y0 的 w 锚 f↔r 转移）+ indexf_n + 幂搬运双实例
  │    （j := PRE (w→d f) / j+1）⟹ next_el r ((next_el f)^j w) = d，故
  │    prev_el r d = (next_el f)^j w；再经同面 congr + fList 定义 ⟹
  │    f_list L ((next_el f)^j w) = (next_el f)^(j+1) w = d。
  │ ② `prevElConstBetwnZtranYtransSucSpine`（KBWPBHQ.hl:1620-1667
  │    prev_el_const_betwn_ztran_ytrans_suc）：marked ∧ f,w ∧ ¬final(i+1) ∧
  │    d ∈ f ∧ z→d f ≤ z→l'y(i+1) f ∧ 0 < z→d f ⇒ f_list L (prev_el r d) = d。
  │    证（HOL 同构）：结构同 ①，锚换成 zᵢ：indexf_n（z→d）+ 幂搬运改由
  │    betwn_ztran_ytrans_suc_const（nb7）双实例（z→d / j，界由 z→ys）+
  │    PNXVWFS2（zᵢ ∈ r）+ 同面 congr + fList 定义。
  │ ③ `exsitsZtransLeCountSpine`（KBWPBHQ.hl:1672-1726 EXSITS_ZTRANS_LE_COUNT）：
  │    marked ∧ d ∈ r ∧ d ∈ f ∧ transform_count = t ∧
  │    ¬(f_list L (prev_el r d) = d) ⇒ ∀ i, 0 < w→d f ∧ w→d f ≤ w→l'y(i) f
  │    ∧ i < t ⇒ ∃ j, l'z(j) = d ∧ j < t。
  │    证（HOL 同构，对 i 归纳）：零支 ① 反证；步支三分——≤ 支 IH；
  │    = 支 indexf_n×2；> 支再三分：< 支 CASES1 反证 / = 支（w→z = w→d）
  │    indexf_n×2 取 j := i / > 支 indexf_add_left×2 + ② 反证。
  │ ④ `prevElConstBetwnZtranWSucSpine`（KBWPBHQ.hl:1730-1789
  │    prev_el_const_betwn_ztran_w_suc）：marked ∧ d ∈ f ∧ 0 < t ∧
  │    transform_count = t ∧ w ∧ indexf w (l'z(PRE t)) f < indexf w d f ⇒
  │    f_list L (prev_el r d) = d。
  │    证（HOL 同构）：i := PRE t；w = z 支与 PPLHULJ 相抵；主支
  │    indexf_add_left[w;z;d] + indexf_antisym 界（0 < z→d、z→d ≤ z→w）+
  │    CASES2（nb8）双实例（z→d / j := PRE (z→d)）+ PNXVWFS2 +
  │    prev_el_nextEl + 同面 congr + fList 定义。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ pplhuljV0 / aq10_memNextMarkInface / indexf_const_le_f（nb8）/
  │ transformCountSpineNot / finalListInductSpine / nextElPowerTransEqFSpine
  │ （nb3）/ betwnZtranYtransSucConstSpine（nb7）/ cases2Spine（nb8）/
  │ pnxvwfs2Spine（nb7）/ indexfN / nextElnIndexf / memPowerNextEl /
  │ prevEl_nextEl（TameLp:4921）/ findFaceDarts_congr_of_mem /
  │ fListPowEqNextElPow / TameList3 indexf 族）同世界零混合；BEq 世界：
  │ nextEl 全走环境实例（instBEqProd；fList 定义体内的烘焙实例同此），
  │ prevEl 经 prevEl_nextEl 桥接通（见 nb9 件 2 头注）。零 Dart 载体件。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqPrev2
import Kepler.Text.TameSpine.Reduction3KbwpbhqCases2

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts prevEl)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup findFaceDarts_congr_of_mem)

/-! ## §1 prev_el_const_le_indexf_y0（KBWPBHQ.hl:1569-1616） -/

/-- **HOL `Kbwpbhq.prev_el_const_le_indexf_y0`**（KBWPBHQ.hl:1569-1616）：
`marked ∧ d ∈ f ∧ 0 < w→d f ∧ w→d f ≤ w→l'y(0) f ∧ 0 < transform_count ⇒
f_list L (prev_el r d) = d`。证（HOL 同构；详见文件头 ①）。 -/
theorem prevElConstLeIndexfY0Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hdf : d ∈ f)
    (hpos : 0 < indexf w d f)
    (hle : indexf w d f ≤ indexf w (ytransSpine L N r x 0) f)
    (ht0 : 0 < transformCountSpine L N r x) :
    fList L (prevEl r d) = d := by
  have hf0 : ¬ finalListSpine L (rtransSpine L N r x 0) :=
    transformCountSpineNot L N r x ht0
  have hf0r : ¬ finalListSpine L r := hf0
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  have hCd := indexfConstLeFSpine L hL hta hgn hm 0 hf0 hfind hw hdf hle
  obtain ⟨hy0f0, -, -⟩ := pplhuljV0 L hL hgn hunL hm hf0r
  rw [hfind] at hy0f0
  have hy0f : ytransSpine L N r x 0 ∈ f := hy0f0
  have hCy := indexfConstLeFSpine L hL hta hgn hm 0 hf0 hfind hw hy0f
    (le_refl _)
  rw [show rtransSpine L N r x 0 = r from rfl] at hCd
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hwr : w ∈ r := by
    have h := nextMarkMemRTransSpine L hL hgn hta hm 0
    rw [show rtransSpine L N r x 0 = r from rfl, hfind, hw] at h
    exact h
  -- 幂搬运（j / j+1）
  obtain ⟨j, hj⟩ : ∃ j, indexf w d f = j + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hb_j : j ≤ indexf w (ytransSpine L N r x 0) (rtransSpine L N r x 0) := by
    omega
  have hpow_j := nextElPowerTransEqFSpine L hL hta hgn hm 0 hf0 hfind hw
    (n := j) hb_j
  have hb_s : j + 1 ≤ indexf w (ytransSpine L N r x 0) (rtransSpine L N r x 0) := by
    omega
  have hpow_s := nextElPowerTransEqFSpine L hL hta hgn hm 0 hf0 hfind hw
    (n := j + 1) hb_s
  rw [show rtransSpine L N r x 0 = r from rfl, hfind] at hpow_j hpow_s
  have hd_eq : (nextEl f)^[j + 1] w = d := by
    rw [← hj]
    exact indexfN hwf hdf hfnd
  have hnext_rd : nextEl r ((nextEl f)^[j] w) = d := by
    calc nextEl r ((nextEl f)^[j] w)
        = nextEl r ((nextEl r)^[j] w) := by rw [hpow_j]
      _ = (nextEl r)^[j + 1] w := by
            rw [← Function.iterate_succ_apply' (nextEl r) j w]
      _ = (nextEl f)^[j + 1] w := hpow_s
      _ = d := hd_eq
  have hmemr : (nextEl f)^[j] w ∈ r := by
    have h := memPowerNextEl hwr j
    rwa [hpow_j] at h
  have hpv : prevEl r d = (nextEl f)^[j] w := by
    rw [← hnext_rd]
    exact Kepler.Text.TameLp.prevEl_nextEl hrnd hmemr
  rw [hpv]
  -- f_list L ((next_el f)^[j] w) = d
  have hmemf : (nextEl f)^[j] w ∈ f := memPowerNextEl hwf j
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hdfx : (nextEl f)^[j] w ∈ findFaceDarts L x := by
    rw [hfind]
    exact hmemf
  have hcong : findFaceDarts L ((nextEl f)^[j] w) = f :=
    (findFaceDarts_congr_of_mem hL.1 hxd hdfx).trans hfind
  show nextEl (findFaceDarts L ((nextEl f)^[j] w)) ((nextEl f)^[j] w) = d
  rw [hcong]
  rw [← Function.iterate_succ_apply' (nextEl f) j w]
  exact hd_eq

/-! ## §2 prev_el_const_betwn_ztran_ytrans_suc（KBWPBHQ.hl:1620-1667） -/

/-- **HOL `Kbwpbhq.prev_el_const_betwn_ztran_ytrans_suc`**（KBWPBHQ.hl:1620-1667）：
`marked ∧ f,w ∧ ¬final(i+1) ∧ d ∈ f ∧ z→d f ≤ z→l'y(i+1) f ∧ 0 < z→d f ⇒
f_list L (prev_el r d) = d`。证（HOL 同构；详见文件头 ②）。 -/
theorem prevElConstBetwnZtranYtransSucSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (i : ℕ) (hfs : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {d : ℕ × ℕ} (hdf : d ∈ f)
    (hle : indexf (ztransSpine L N r x i) d f
      ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x (i + 1)) f)
    (hpos : 0 < indexf (ztransSpine L N r x i) d f) :
    fList L (prevEl r d) = d := by
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    finalListInductSpine L N r x i hfs
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  obtain ⟨-, hzf0, -⟩ := pplhuljV0 L hL hgn hunL (aqiunpp3 L hL i hta hgn hm) hfi
  rw [hfind] at hzf0
  have hzif : ztransSpine L N r x i ∈ f := hzf0
  obtain ⟨j, hj⟩ : ∃ j, indexf (ztransSpine L N r x i) d f = j + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hb1 := betwnZtranYtransSucConstSpine L hL hta hgn hunL hm i hfs hfind hw
    (n := indexf (ztransSpine L N r x i) d f) (by omega)
  rw [hj] at hb1
  have hb2 := betwnZtranYtransSucConstSpine L hL hta hgn hunL hm i hfs hfind hw
    (n := j) (by omega)
  have hd_eq : (nextEl f)^[j + 1] (ztransSpine L N r x i) = d := by
    rw [← hj]
    exact indexfN hzif hdf hfnd
  have hnext_rd : nextEl r ((nextEl f)^[j] (ztransSpine L N r x i)) = d := by
    calc nextEl r ((nextEl f)^[j] (ztransSpine L N r x i))
        = nextEl r ((nextEl r)^[j] (ztransSpine L N r x i)) := by rw [hb2]
      _ = (nextEl r)^[j + 1] (ztransSpine L N r x i) := by
            rw [← Function.iterate_succ_apply' (nextEl r) j
              (ztransSpine L N r x i)]
      _ = (nextEl f)^[j + 1] (ztransSpine L N r x i) := hb1
      _ = d := hd_eq
  have hzir : ztransSpine L N r x i ∈ r := pnxvwfs2Spine L hL hta hgn hunL hm i hfi
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hmemr : (nextEl f)^[j] (ztransSpine L N r x i) ∈ r := by
    have h := memPowerNextEl hzir j
    rwa [hb2] at h
  have hpv : prevEl r d = (nextEl f)^[j] (ztransSpine L N r x i) := by
    rw [← hnext_rd]
    exact Kepler.Text.TameLp.prevEl_nextEl hrnd hmemr
  rw [hpv]
  have hmemf : (nextEl f)^[j] (ztransSpine L N r x i) ∈ f := memPowerNextEl hzif j
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hdfx : (nextEl f)^[j] (ztransSpine L N r x i) ∈ findFaceDarts L x := by
    rw [hfind]
    exact hmemf
  have hcong : findFaceDarts L ((nextEl f)^[j] (ztransSpine L N r x i)) = f :=
    (findFaceDarts_congr_of_mem hL.1 hxd hdfx).trans hfind
  show nextEl (findFaceDarts L ((nextEl f)^[j] (ztransSpine L N r x i)))
    ((nextEl f)^[j] (ztransSpine L N r x i)) = d
  rw [hcong]
  rw [← Function.iterate_succ_apply' (nextEl f) j (ztransSpine L N r x i)]
  exact hd_eq

/-! ## §3 EXSITS_ZTRANS_LE_COUNT（KBWPBHQ.hl:1672-1726） -/

/-- **HOL `Kbwpbhq.EXSITS_ZTRANS_LE_COUNT`**（KBWPBHQ.hl:1672-1726）：
`marked ∧ d ∈ r ∧ d ∈ f ∧ transform_count = t ∧
¬(f_list L (prev_el r d) = d) ⇒ ∀ i, 0 < w→d f ∧ w→d f ≤ w→l'y(i) f ∧ i < t ⇒
∃ j, l'z(j) = d ∧ j < t`。证（HOL 同构；详见文件头 ③）。 -/
theorem exsitsZtransLeCountSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {t : ℕ} (ht : transformCountSpine L N r x = t)
    {d : ℕ × ℕ} (hdr : d ∈ r) (hdf : d ∈ f)
    (hne : ¬ (fList L (prevEl r d) = d)) :
    ∀ i, 0 < indexf w d f ∧ indexf w d f ≤ indexf w (ytransSpine L N r x i) f
        ∧ i < t →
      ∃ j, ztransSpine L N r x j = d ∧ j < t := by
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  intro i
  induction i with
  | zero =>
    rintro ⟨h1, h2, h3⟩
    exfalso
    exact hne (prevElConstLeIndexfY0Spine L hL hta hgn hunL hm hfind hw hdf
      h1 h2 (by omega))
  | succ i ih =>
    rintro ⟨h1, h2, h3⟩
    have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
      transformCountSpineNot L N r x (by omega)
    have hfs : ¬ finalListSpine L (rtransSpine L N r x (i + 1)) :=
      transformCountSpineNot L N r x (by omega)
    rcases lt_trichotomy (indexf w d f)
      (indexf w (ytransSpine L N r x i) f) with hlt | heq | hgt
    · exact ih ⟨h1, Nat.le_of_lt hlt, by omega⟩
    · exact ih ⟨h1, Nat.le_of_eq heq, by omega⟩
    · -- w→y < w→d：对 w→d 与 w→z 三分
      have hmr := aqiunpp3 L hL i hta hgn hm
      obtain ⟨-, hzf0, -⟩ := pplhuljV0 L hL hgn hunL hmr hfi
      rw [hfind] at hzf0
      have hzif : ztransSpine L N r x i ∈ f := hzf0
      have hQ := qcdvkeaTowerSpine L hL hta hgn hm i hfs hfind hw
      rcases lt_trichotomy (indexf w d f)
        (indexf w (ztransSpine L N r x i) f) with hlt' | heq' | hgt'
      · exfalso
        exact cases1 L hL hta hgn hunL hm hfind hw hfi hlt' hgt hdf hdr
      · refine ⟨i, ?_, by omega⟩
        have e1 := indexfN hwf hzif hfnd
        have e2 := indexfN hwf hdf hfnd
        rw [heq'] at e2
        exact e1.symm.trans e2
      · exfalso
        have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
        obtain ⟨hysf0, -, -⟩ := pplhuljV0 L hL hgn hunL hmr1 hfs
        rw [hfind] at hysf0
        have hysf : ytransSpine L N r x (i + 1) ∈ f := hysf0
        have hA1 := indexfAddLeft hwf hzif hdf (by omega)
        have hA2 := indexfAddLeft hwf hzif hysf hQ
        exact hne (prevElConstBetwnZtranYtransSucSpine L hL hta hgn hunL hm
          hfind hw i hfs hdf (by omega) (by omega))

/-! ## §4 prev_el_const_betwn_ztran_w_suc（KBWPBHQ.hl:1730-1789） -/

/-- **HOL `Kbwpbhq.prev_el_const_betwn_ztran_w_suc`**（KBWPBHQ.hl:1730-1789）：
`marked ∧ d ∈ f ∧ 0 < t ∧ transform_count = t ∧ f,w ∧
indexf w (l'z(PRE t)) f < indexf w d f ⇒ f_list L (prev_el r d) = d`
（PRE t ↦ t − 1）。证（HOL 同构；详见文件头 ④）。 -/
theorem prevElConstBetwnZtranWSucSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {t : ℕ} (ht0 : 0 < t) (ht : transformCountSpine L N r x = t)
    {d : ℕ × ℕ} (hdf : d ∈ f)
    (hlt : indexf w (ztransSpine L N r x (t - 1)) f < indexf w d f) :
    fList L (prevEl r d) = d := by
  have hfi : ¬ finalListSpine L (rtransSpine L N r x (t - 1)) :=
    transformCountSpineNot L N r x (by omega)
  have hmr := aqiunpp3 L hL (t - 1) hta hgn hm
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  obtain ⟨-, hzf0, hlt0⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  rw [hfind] at hzf0 hlt0
  rw [hw] at hlt0
  have hzif : ztransSpine L N r x (t - 1) ∈ f := hzf0
  have hlyz : indexf w (ytransSpine L N r x (t - 1)) f
      < indexf w (ztransSpine L N r x (t - 1)) f := hlt0
  by_cases hwz : w = ztransSpine L N r x (t - 1)
  · exfalso
    have h0 : indexf w (ztransSpine L N r x (t - 1)) f = 0 := by
      rw [hwz]
      exact indexfRefl hzif
    omega
  · have hanti := indexfAntisym hwf hzif hwz
    have hwdlt := indexfLtSizel hwf hdf
    have hA := indexfAddLeft hwf hzif hdf (Nat.le_of_lt hlt)
    have hzdpos : 0 < indexf (ztransSpine L N r x (t - 1)) d f := by omega
    have hzdw : indexf (ztransSpine L N r x (t - 1)) d f
        ≤ indexf (ztransSpine L N r x (t - 1)) w f := by omega
    obtain ⟨j, hj⟩ : ∃ j, indexf (ztransSpine L N r x (t - 1)) d f = j + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hzdpos).symm⟩
    have hc1 := cases2Spine L hL hta hgn hunL hm hfind hw ht0 ht
      (n := indexf (ztransSpine L N r x (t - 1)) d f) (by omega)
    rw [hj] at hc1
    have hc2 := cases2Spine L hL hta hgn hunL hm hfind hw ht0 ht
      (n := j) (by omega)
    have hd_eq : (nextEl f)^[j + 1] (ztransSpine L N r x (t - 1)) = d := by
      rw [← hj]
      exact indexfN hzif hdf hfnd
    have hnext_rd : nextEl r ((nextEl f)^[j] (ztransSpine L N r x (t - 1)))
        = d := by
      calc nextEl r ((nextEl f)^[j] (ztransSpine L N r x (t - 1)))
          = nextEl r ((nextEl r)^[j] (ztransSpine L N r x (t - 1))) := by rw [hc2]
        _ = (nextEl r)^[j + 1] (ztransSpine L N r x (t - 1)) := by
              rw [← Function.iterate_succ_apply' (nextEl r) j
                (ztransSpine L N r x (t - 1))]
        _ = (nextEl f)^[j + 1] (ztransSpine L N r x (t - 1)) := hc1
        _ = d := hd_eq
    have hzir : ztransSpine L N r x (t - 1) ∈ r :=
      pnxvwfs2Spine L hL hta hgn hunL hm (t - 1) hfi
    have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
    have hmemr : (nextEl f)^[j] (ztransSpine L N r x (t - 1)) ∈ r := by
      have h := memPowerNextEl hzir j
      rwa [hc2] at h
    have hpv : prevEl r d = (nextEl f)^[j] (ztransSpine L N r x (t - 1)) := by
      rw [← hnext_rd]
      exact Kepler.Text.TameLp.prevEl_nextEl hrnd hmemr
    rw [hpv]
    have hmemf : (nextEl f)^[j] (ztransSpine L N r x (t - 1)) ∈ f :=
      memPowerNextEl hzif j
    have hxd : x ∈ listOfDarts L :=
      normalListListOfDarts hm.1.2.1 x
        (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
    have hdfx : (nextEl f)^[j] (ztransSpine L N r x (t - 1)) ∈ findFaceDarts L x := by
      rw [hfind]
      exact hmemf
    have hcong : findFaceDarts L ((nextEl f)^[j] (ztransSpine L N r x (t - 1))) = f :=
      (findFaceDarts_congr_of_mem hL.1 hxd hdfx).trans hfind
    show nextEl (findFaceDarts L ((nextEl f)^[j] (ztransSpine L N r x (t - 1))))
      ((nextEl f)^[j] (ztransSpine L N r x (t - 1))) = d
    rw [hcong]
    rw [← Function.iterate_succ_apply' (nextEl f) j
      (ztransSpine L N r x (t - 1))]
    exact hd_eq

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.prevElConstLeIndexfY0Spine
#print axioms Kepler.Text.TameSpine.prevElConstBetwnZtranYtransSucSpine
#print axioms Kepler.Text.TameSpine.exsitsZtransLeCountSpine
#print axioms Kepler.Text.TameSpine.prevElConstBetwnZtranWSucSpine
