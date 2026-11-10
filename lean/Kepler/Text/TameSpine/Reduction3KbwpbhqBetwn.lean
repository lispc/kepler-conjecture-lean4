/-
  Kepler.Text.TameSpine.Reduction3KbwpbhqBetwn — tame-corr nb7：KBWPBHQ 章
  betwn_ztran_ytrans_suc_const 段三件（J4 关键路径；余量段）。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ ① `indexfConstLeFSpine`（KBWPBHQ.hl:490-523 indexf_const_le_f）：
  │    ¬final(i) ∧ MEM d f ∧ indexf w d f ≤ indexf w (l'y(i)) f ⇒
  │    indexf w d r₁ = indexf w d f（面侧界形；nb3
  │    indexfConstLeIndexfYtransSpine 是 loop 侧界形孪生）。
  │    证（HOL 同构）：indexf_const_le_indexf_ytrans@y（自反）+ indexf_n
  │    （f 上）+ next_el_power_trans_eq_f（nb3）@n:=w→d f +
  │    MEM_POWER_NEXT_EL + indexf_lt_sizel + next_eln_indexf（r₁ 上）。
  │ ② `betwnZtranYtransSucConstSpine`（KBWPBHQ.hl:623-699
  │    betwn_ztran_ytrans_suc_const，77 HOL 行）：¬final(i+1) ∧
  │    n ≤ indexf (l'z(i)) (l'y(i+1)) f ⇒
  │    (next_el r)^n (l'z(i)) = (next_el f)^n (l'z(i))。
  │    证（HOL 同构，d := (next_el f)^n z）：
  │    · f 侧：QCDVKEA + indexf_add_left[w;z;ys;f] ⟹ w→d f = n + w→z f；
  │    · r₂ 侧：next_el_power_trans_eq_f@(i+1) 双实例（幂加法拆分）
  │      ⟹ (next_el r₂)^n z = d、d ∈ r₂、z→d r₂ = n；
  │      z→ys r₂ = z→ys f（① + indexf_const_le_indexf_ytrans + 双 add_left）；
  │    · r₁ 侧：d ∈ r₁（indexf_in_rtrans_suc_not_rtrans 反证）+
  │      trans_indexf_suc 双实例（z 锚自反界）⟹ z→d r₁ = n ≤ z→ys r₁；
  │      ytran_suc_betwn_z_z_suc + ztrans_suc_in_ztran_w + w_betwn conj1
  │      ⟹ z→d r₁ ≤ z→l'y(0) r₁；
  │    · r 侧：PBFLHET（d ∈ r ∧ z→d r₁ = z→d r）+ PNXVWFS2（z ∈ r）+
  │      indexf_n（r 上）收口。
  │ ③ `nextElConstBetwnZtranYtransSucSpine`（KBWPBHQ.hl:703-726
  │    next_el_const_betwn_ztran_ytrans_suc）：¬final(i+1) ∧ MEM d f ∧
  │    indexf (l'z(i)) d f < indexf (l'z(i)) (l'y(i+1)) f ⇒
  │    next_el r d = f_list L d。证 = ② 双实例（n := z→d f 与 +1）+
  │    indexf_n + 同面等表 congr + fListPowEqNextElPow@1。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ pplhuljV0 / qcdvkeaTowerSpine / nextElPowerTransEqFSpine /
  │ indexfConstLeIndexfYtransSpine / indexfInRtransSucNotRtrans /
  │ transIndexfSucSpine / ztransInSucSpine / memZtransRtransSpine /
  │ ytransInSucSpine / ytranSucBetwnZZSucSpine /
  │ ztransSucInZtranWSpineClosed / wBetwnZtransYtran0Spine / pbflhetSpine
  │ / pnxvwfs2Spine / fListPowEqNextElPow / TameList3 indexf 族 /
  │ memPowerNextEl / TameLp 面件）同世界零混合；零 Dart 载体件。
  │ 全文件默认心跳、linter 全开（零 set_option 覆盖）。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Pnxvwfs

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup findFaceDarts_congr_of_mem)

/-! ## §1 indexf_const_le_f（KBWPBHQ.hl:490-523） -/

/-- **HOL `Kbwpbhq.indexf_const_le_f`**（KBWPBHQ.hl:490-523）塔层 i 形：
`¬final(i) ∧ MEM d f ∧ indexf w d f ≤ indexf w (l'y(i)) f ⇒
indexf w d r₁ = indexf w d f`。
证（HOL 同构）：indexf_n（f 上）给 (next_el f)^(w→d f) w = d；
next_el_power_trans_eq_f（nb3）把该幂搬到 r₁（界 = 前提 +
indexf_const_le_indexf_ytrans@y 自反）；MEM_POWER_NEXT_EL 给 d ∈ r₁；
next_eln_indexf（r₁ 上，界 < sizel 由 indexf_lt_sizel）收口。 -/
theorem indexfConstLeFSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd : d ∈ f)
    (hle : indexf w d f ≤ indexf w (ytransSpine L N r x i) f) :
    indexf w d (rtransSpine L N r x i) = indexf w d f := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hy : ytransSpine L N r x i ∈ rtransSpine L N r x i :=
    ytransMemRtrans L hL hgn hmr hf
  have hC : indexf w (ytransSpine L N r x i) (rtransSpine L N r x i)
      = indexf w (ytransSpine L N r x i) f :=
    indexfConstLeIndexfYtransSpine L hL hta hgn hm i hf hfind hw hy (le_refl _)
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  have hdn : (nextEl f)^[indexf w d f] w = d := indexfN hwf hd hfnd
  have hpow := nextElPowerTransEqFSpine L hL hta hgn hm i hf hfind hw
    (n := indexf w d f) (by omega)
  rw [hfind, hdn] at hpow
  have hwr : w ∈ rtransSpine L N r x i := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm i
  have hrnd : (rtransSpine L N r x i).Nodup :=
    (normalListUniqNonnil hmr.1.2.1 hmr.1.2.2.1).1
  have hdr : d ∈ rtransSpine L N r x i := by
    have h := memPowerNextEl hwr (indexf w d f)
    rw [hpow] at h
    exact h
  have hlt : indexf w d f < (rtransSpine L N r x i).length := by
    have := indexfLtSizel hwr hy
    omega
  exact nextElnIndexf hwr hdr hrnd hpow hlt

/-! ## §2 betwn_ztran_ytrans_suc_const（KBWPBHQ.hl:623-699） -/

/-- **HOL `Kbwpbhq.betwn_ztran_ytrans_suc_const`**（KBWPBHQ.hl:623-699）
塔层 i 形：`¬final(i+1) ∧ n ≤ indexf (l'z(i)) (l'y(i+1)) f ⇒
(next_el r)^n (l'z(i)) = (next_el f)^n (l'z(i))`。
证（HOL 同构，d := (next_el f)^n z；f 侧 → r₂ 侧 → r₁ 侧 → r 侧四段，
详见文件头 ②）。 -/
theorem betwnZtranYtransSucConstSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) {n : ℕ}
    (hn : n ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x (i + 1)) f) :
    (nextEl r)^[n] (ztransSpine L N r x i)
      = (nextEl f)^[n] (ztransSpine L N r x i) := by
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    finalListInductSpine L N r x i hf
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
  -- 面件：w, z, ys ∈ f；uniq f
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  obtain ⟨-, hzf, -⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  rw [hfind] at hzf
  have hzif : ztransSpine L N r x i ∈ f := hzf
  obtain ⟨hyf1, -, -⟩ := pplhuljV0 L hL hgn hunL hmr1 hf
  rw [hfind] at hyf1
  have hysf : ytransSpine L N r x (i + 1) ∈ f := hyf1
  -- d := (next_el f)^n z
  obtain ⟨d, hd⟩ : ∃ d, d = (nextEl f)^[n] (ztransSpine L N r x i) := ⟨_, rfl⟩
  have hdf : d ∈ f := by
    rw [hd]
    exact memPowerNextEl hzif n
  -- f 侧：w→z + z→ys = w→ys；w→d = n + w→z
  have hQ := qcdvkeaTowerSpine L hL hta hgn hm i hf hfind hw
  have hA := indexfAddLeft hwf hzif hysf hQ
  have hyslt := indexfLtSizel hwf hysf
  have hzn : (nextEl f)^[indexf w (ztransSpine L N r x i) f] w
      = ztransSpine L N r x i := indexfN hwf hzif hfnd
  have hwd : indexf w d f = n + indexf w (ztransSpine L N r x i) f := by
    refine nextElnIndexf hwf hdf hfnd ?_ (by omega)
    rw [Function.iterate_add_apply, hzn]
    exact hd.symm
  -- r₂ 侧：幂搬运（next_el_power_trans_eq_f@(i+1) 双实例）
  have hysrs : ytransSpine L N r x (i + 1) ∈ rtransSpine L N r x (i + 1) :=
    ytransMemRtrans L hL hgn hmr1 hf
  have hCys : indexf w (ytransSpine L N r x (i + 1))
        (rtransSpine L N r x (i + 1))
      = indexf w (ytransSpine L N r x (i + 1)) f :=
    indexfConstLeIndexfYtransSpine L hL hta hgn hm (i + 1) hf hfind hw
      hysrs (le_refl _)
  have hpow1 := nextElPowerTransEqFSpine L hL hta hgn hm (i + 1) hf hfind hw
    (n := indexf w (ztransSpine L N r x i) f) (by omega)
  rw [hfind, hzn] at hpow1
  have hR : (nextEl (rtransSpine L N r x (i + 1)))^[n] (ztransSpine L N r x i)
      = d := by
    have h2 := nextElPowerTransEqFSpine L hL hta hgn hm (i + 1) hf hfind hw
      (n := n + indexf w (ztransSpine L N r x i) f) (by omega)
    rw [hfind,
      Function.iterate_add_apply (nextEl (rtransSpine L N r x (i + 1))),
      Function.iterate_add_apply (nextEl f), hzn, hpow1] at h2
    rw [hd]
    exact h2
  have hCzi := indexfConstLeFSpine L hL hta hgn hm (i + 1) hf hfind hw hzif hQ
  have hwrs : w ∈ rtransSpine L N r x (i + 1) := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm (i + 1)
  have hzirs : ztransSpine L N r x i ∈ rtransSpine L N r x (i + 1) :=
    ztransInSucSpine L hL hta hgn hm i hfi
  have hA' := indexfAddLeft hwrs hzirs hysrs (by omega)
  -- r₁ 侧：trans_indexf_suc 双实例（z 锚自反界）
  have hziri : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hfi
  have hysri : ytransSpine L N r x (i + 1) ∈ rtransSpine L N r x i :=
    ytransInSucSpine L hL hta hgn hunL hm i hf hfind hw
  have hzz : indexf (ztransSpine L N r x i) (ztransSpine L N r x i)
      (rtransSpine L N r x i) = 0 := indexfRefl hziri
  have hT1 := transIndexfSucSpine L hL hta hgn hunL hm i hfi hysri hziri
    hysrs hzirs (by omega)
  have hB := ytranSucBetwnZZSucSpine L hL hta hgn hunL hm i hf hfind hw
  have hZ := ztransSucInZtranWSpineClosed L hL hta hgn hunL hm i hf hfind hw
  obtain ⟨hW1, -⟩ := wBetwnZtransYtran0Spine L hL hta hgn hunL hm i hfi hfind hw
  have hrsnd : (rtransSpine L N r x (i + 1)).Nodup :=
    (normalListUniqNonnil hmr1.1.2.1 hmr1.1.2.2.1).1
  have hdrs : d ∈ rtransSpine L N r x (i + 1) := by
    have h := memPowerNextEl hzirs n
    rw [hR] at h
    exact h
  have hdri : d ∈ rtransSpine L N r x i := by
    by_contra hnot
    have h := (indexfInRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw
      hdrs hnot).1
    omega
  have hT2 := transIndexfSucSpine L hL hta hgn hunL hm i hfi hdri hziri
    hdrs hzirs (by omega)
  have hnrs : n < (rtransSpine L N r x (i + 1)).length := by
    have := indexfLtSizel hzirs hysrs
    omega
  have hidrs : indexf (ztransSpine L N r x i) d (rtransSpine L N r x (i + 1))
      = n := nextElnIndexf hzirs hdrs hrsnd hR hnrs
  -- r 侧：PBFLHET + PNXVWFS2 + indexf_n
  obtain ⟨hdr, heq⟩ := pbflhetSpine L hL hta hgn hunL hm i hfi hdri (by omega)
  have hzir : ztransSpine L N r x i ∈ r :=
    pnxvwfs2Spine L hL hta hgn hunL hm i hfi
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hfin := indexfN hzir hdr hrnd
  have hidx : indexf (ztransSpine L N r x i) d r = n := by omega
  rw [hidx] at hfin
  rw [← hd]
  exact hfin

/-! ## §3 next_el_const_betwn_ztran_ytrans_suc（KBWPBHQ.hl:703-726） -/

/-- **HOL `Kbwpbhq.next_el_const_betwn_ztran_ytrans_suc`**
（KBWPBHQ.hl:703-726）塔层 i 形：`¬final(i+1) ∧ MEM d f ∧
indexf (l'z(i)) d f < indexf (l'z(i)) (l'y(i+1)) f ⇒
next_el r d = f_list L d`。
证 = betwn_ztran_ytrans_suc_const 双实例（n := z→d f 与 n+1）+
indexf_n（f 上折回 d）+ 同面等表 congr + fListPowEqNextElPow@1。 -/
theorem nextElConstBetwnZtranYtransSucSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd : d ∈ f)
    (hlt : indexf (ztransSpine L N r x i) d f
      < indexf (ztransSpine L N r x i) (ytransSpine L N r x (i + 1)) f) :
    nextEl r d = fList L d := by
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    finalListInductSpine L N r x i hf
  have hmr := aqiunpp3 L hL i hta hgn hm
  obtain ⟨-, hzf, -⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  rw [hfind] at hzf
  have hzif : ztransSpine L N r x i ∈ f := hzf
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  have hdn : (nextEl f)^[indexf (ztransSpine L N r x i) d f]
      (ztransSpine L N r x i) = d := indexfN hzif hd hfnd
  have h1 := betwnZtranYtransSucConstSpine L hL hta hgn hunL hm i hf hfind hw
    (n := indexf (ztransSpine L N r x i) d f) (by omega)
  have h2 := betwnZtranYtransSucConstSpine L hL hta hgn hunL hm i hf hfind hw
    (n := indexf (ztransSpine L N r x i) d f + 1) (by omega)
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1, hdn] at h2
  -- f_list L d = next_el (find_face L d) d = next_el f d
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hdfx : d ∈ findFaceDarts L x := by
    rw [hfind]
    exact hd
  have hcong : findFaceDarts L d = f :=
    (findFaceDarts_congr_of_mem hL.1 hxd hdfx).trans hfind
  have hdd : d ∈ findFaceDarts L d := by
    rw [hcong]
    exact hd
  have hfl := fListPowEqNextElPow L hL d hdd 1
  simp only [Function.iterate_one] at hfl
  rw [hcong] at hfl
  rw [h2, hfl]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.indexfConstLeFSpine
#print axioms Kepler.Text.TameSpine.betwnZtranYtransSucConstSpine
#print axioms Kepler.Text.TameSpine.nextElConstBetwnZtranYtransSucSpine
