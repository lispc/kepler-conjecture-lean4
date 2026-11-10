/-
  Kepler.Text.TameSpine.Reduction3KbwpbhqCases2 — tame-corr nb8：KBWPBHQ 章
  CASES2 段（波 A）：in_rtrans_suc_not_rtrans_new 双件塔层形 + CASES2 +
  next_el_const_betwn_ztran_w_suc。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ ① `inRtransSucNotRtransNewSpine`（KBWPBHQ.hl:802-843
  │    in_rtrans_suc_not_rtrans_new）与
  │ ② `indexfInRtransSucNotRtransNewSpine`（KBWPBHQ.hl:844-883
  │    indexf_in_rtrans_suc_not_rtrans_new）：前提 ¬final(i)（**不是**
  │    ¬final(i+1)——CASES2 的 r(i+1) = r(t) 恰为 final 态，nb3 的
  │    PBFLHET:122/166 孪生件前提过强不可用）。证 = V0 形
  │    `inRtransSucNotRtransNewV0`（JcajyduAqSnd:92）塔层 i 直投 +
  │    PPLHULJ + hqymrtx3List + 窗口位置算术（indexf_betwn_eq /
  │    add_left / add_betwn / add_right + omega；nb3 私件
  │    indexfBetweenArith 同款，私件不可跨文件故就地重写）。
  │ ③ `cases2SpineAux`（CASES2 的 i 参数形：transform_count = i+1）与
  │ ④ `cases2Spine`（KBWPBHQ.hl:935-1069 CASES2，135 HOL 行，HOL 逐字
  │    形：0 < t ∧ transform_count = t ∧ n ≤ indexf (ztrans (PRE t)) w f
  │    ⇒ (next_el r)^n (ztrans (PRE t)) = (next_el f)^n (ztrans (PRE t))；
  │    PRE t ↦ t − 1）。证（HOL 同构，d := (next_el f)^n z，rt := r(t)）：
  │    · final 层 rt：final_list_transform_count + final_list_power ⟹
  │      ∀k, (next_el rt)^k z = (next_el f)^k z；sizel_final_list_eq_f +
  │      next_eln_indexf ⟹ z→d rt = n、z→w rt = z→w f；
  │    · d ∈ r₁：n < z→w f 支由 ②（w→d f = n + w→z f，indexf_antisym
  │      供界）反证；n = z→w f 支 d = w（HOL :1020-1022 同分支）；
  │    · r₁ 侧：trans_indexf_suc 双实例（d / w，z 锚自反界）+ w_betwn
  │      conj1 ⟹ z→d r₁ ≤ z→l'y(0) r₁；
  │    · r 侧：PBFLHET + PNXVWFS2 + indexf_n 收口。
  │    w = z 支：与 PPLHULJ（w→y < w→z）+ indexf_refl 矛盾（HOL :963-966）。
  │ ⑤ `nextElConstBetwnZtranWSucSpine`（KBWPBHQ.hl:1072-1110
  │    next_el_const_betwn_ztran_w_suc）：0 < t ∧ transform_count = t ∧
  │    MEM d f ∧ indexf w (ztrans (PRE t)) f ≤ indexf w d f ⇒
  │    next_el r d = f_list L d。证 = indexf_add_left + indexf_antisym
  │    界算术 + CASES2 双实例（n := z→d f 与 n+1）+ 同面 congr +
  │    fListPowEqNextElPow@1（与 nb7 件 17 同构）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ pplhuljV0 / hqymrtx3List / inRtransSucNotRtransNewV0 /
  │ transformCountSpineNot / finalListTransformCountSpine /
  │ sizelFinalListEqF / finalListPower / ztransInSucSpine /
  │ memZtransRtransSpine / nextMarkMemRTransSpine / transIndexfSucSpine /
  │ wBetwnZtransYtran0Spine / pbflhetSpine / pnxvwfs2Spine /
  │ fListPowEqNextElPow / TameList3 indexf 族 / memPowerNextEl /
  │ TameLp 面件）同世界零混合；零 Dart 载体件。
  │ 全文件默认心跳、linter 全开（零 set_option 覆盖）。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqBetwn

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup findFaceDarts_congr_of_mem
  mem_darts_of_mem_findFace)

/-! ## §1 in_rtrans_suc_not_rtrans_new 双件（KBWPBHQ.hl:802-883） -/

/-- **HOL `Kbwpbhq.in_rtrans_suc_not_rtrans_new`**（KBWPBHQ.hl:802-843）
塔层 i 形：`¬final(i) ∧ d ∈ r₂ ∧ d ∉ r₁ ⇒ d ∈ betwn f (l'y(i)) (l'z(i))`。
证 = V0 形 `inRtransSucNotRtransNewV0`（HOJODCM.hl:107）塔层 i 直投
（aqiunpp3 供标记件；l'y 处面表经 congr 换元到 f）。 -/
theorem inRtransSucNotRtransNewSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hfi : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} (hfind : findFaceDarts L x = f)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hd0 : d ∉ rtransSpine L N r x i) :
    d ∈ between f (ytransSpine L N r x i) (ztransSpine L N r x i) := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  obtain ⟨hyf, -, -⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hcongY : findFaceDarts L (lYSpine L (rtransSpine L N r x i) x) = f :=
    (findFaceDarts_congr_of_mem hL.1 hxd hyf).trans hfind
  rw [rtransSuccSpine L N r x i] at hd1
  have hv0 := inRtransSucNotRtransNewV0 L hL hgn hunL hmr hfi hd1 hd0
  rw [hcongY] at hv0
  exact hv0

/-- **HOL `Kbwpbhq.indexf_in_rtrans_suc_not_rtrans_new`**
（KBWPBHQ.hl:844-883）塔层 i 形：`¬final(i) ∧ d ∈ r₂ ∧ d ∉ r₁ ⇒
indexf w d f < indexf w (l'z(i)) f ∧ indexf w (l'y(i)) f < indexf w d f`。
证 = 上件（窗口成员）+ PPLHULJ（w→y < w→z）+ y ≠ z（hqymrtx3List）+
窗口位置算术（indexf_betwn_eq / add_left / add_betwn / add_right）。 -/
theorem indexfInRtransSucNotRtransNewSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hfi : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hd0 : d ∉ rtransSpine L N r x i) :
    indexf w d f < indexf w (ztransSpine L N r x i) f
      ∧ indexf w (ytransSpine L N r x i) f < indexf w d f := by
  have hbet := inRtransSucNotRtransNewSpine L hL hta hgn hunL hm i hfi hfind
    hd1 hd0
  have hmr := aqiunpp3 L hL i hta hgn hm
  obtain ⟨hyf0, hzf0, hlt0⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  rw [hfind] at hlt0 hyf0 hzf0
  rw [hw] at hlt0
  have hyf : ytransSpine L N r x i ∈ f := hyf0
  have hzf : ztransSpine L N r x i ∈ f := hzf0
  have hlt : indexf w (ytransSpine L N r x i) f
      < indexf w (ztransSpine L N r x i) f := hlt0
  have hne : ytransSpine L N r x i ≠ ztransSpine L N r x i :=
    hqymrtx3List L hL hgn hunL hmr hfi
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  -- 窗口位置算术
  obtain ⟨hp1, hp2⟩ := (indexfBetwnEq hne hfnd hyf hzf).mp hbet
  have hA := indexfAddLeft hwf hyf hzf (Nat.le_of_lt hlt)
  have hB := indexfAddBetwn hne hfnd hyf hbet hzf
  have hdf : d ∈ f := betwnMem hbet
  have hC := indexfAddRight hwf hdf hzf (by omega)
  omega

/-! ## §2 CASES2（KBWPBHQ.hl:935-1069） -/

/-- CASES2 的 i 参数形（`transform_count = i + 1`，即 HOL 的 i := PRE t）：
`n ≤ indexf (l'z(i)) w f ⇒ (next_el r)^n (l'z(i)) = (next_el f)^n (l'z(i))`。
证体与 HOL :945-1069 同构（详见文件头 ④）。 -/
theorem cases2SpineAux (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hc : transformCountSpine L N r x = i + 1)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) {n : ℕ}
    (hn : n ≤ indexf (ztransSpine L N r x i) w f) :
    (nextEl r)^[n] (ztransSpine L N r x i)
      = (nextEl f)^[n] (ztransSpine L N r x i) := by
  -- 层态：¬final(i)、final(i+1)、|r(i+1)| = |f|
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    transformCountSpineNot L N r x (by omega)
  have hft : finalListSpine L (rtransSpine L N r x (i + 1)) :=
    finalListTransformCountSpine L hL hta hgn hm hc
  have hlen : (rtransSpine L N r x (i + 1)).length = f.length := by
    rw [← hfind]
    exact sizelFinalListEqF L hL hta hgn hm hc
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
  have hrtnd : (rtransSpine L N r x (i + 1)).Nodup :=
    (normalListUniqNonnil hmr1.1.2.1 hmr1.1.2.2.1).1
  -- 面件
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  obtain ⟨-, hzf0, hlt0⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hzid : ztransSpine L N r x i ∈ listOfDarts L :=
    mem_darts_of_mem_findFace L hzf0
  have hcongz : findFaceDarts L (ztransSpine L N r x i) = f :=
    (findFaceDarts_congr_of_mem hL.1 hxd hzf0).trans hfind
  rw [hfind] at hzf0 hlt0
  rw [hw] at hlt0
  have hzif : ztransSpine L N r x i ∈ f := hzf0
  have hlt : indexf w (ytransSpine L N r x i) f
      < indexf w (ztransSpine L N r x i) f := hlt0
  -- w ≠ z（HOL :963-966：w = z 支与 PPLHULJ + indexf_refl 矛盾）
  have hwne : w ≠ ztransSpine L N r x i := by
    intro h
    have h0 : indexf w (ztransSpine L N r x i) f = 0 := by
      rw [h]
      exact indexfRefl hzif
    omega
  have hanti := indexfAntisym hwf hzif hwne
  have hzn : (nextEl f)^[indexf w (ztransSpine L N r x i) f] w
      = ztransSpine L N r x i := indexfN hwf hzif hfnd
  have hzwlt := indexfLtSizel hzif hwf
  -- final 层 rt：幂一致（final_list_power）
  have hzirt : ztransSpine L N r x i ∈ rtransSpine L N r x (i + 1) :=
    ztransInSucSpine L hL hta hgn hm i hfi
  have hpowt : ∀ k : ℕ,
      (nextEl (rtransSpine L N r x (i + 1)))^[k] (ztransSpine L N r x i)
        = (nextEl f)^[k] (ztransSpine L N r x i) := by
    intro k
    have h := (finalListPower hL hft hzirt hrtnd hzid k).2.2
    rw [hcongz] at h
    exact h
  -- d := (next_el f)^n z
  obtain ⟨d, hd⟩ : ∃ d, d = (nextEl f)^[n] (ztransSpine L N r x i) := ⟨_, rfl⟩
  have hdf : d ∈ f := by
    rw [hd]
    exact memPowerNextEl hzif n
  have hRt : (nextEl (rtransSpine L N r x (i + 1)))^[n] (ztransSpine L N r x i)
      = d := by
    rw [hpowt n]
    exact hd.symm
  have hdrt : d ∈ rtransSpine L N r x (i + 1) := by
    have h := memPowerNextEl hzirt n
    rw [hRt] at h
    exact h
  have hidrt : indexf (ztransSpine L N r x i) d (rtransSpine L N r x (i + 1))
      = n := nextElnIndexf hzirt hdrt hrtnd hRt (by omega)
  -- w 在 rt / r₁ 上的 z-index
  have hwrt : w ∈ rtransSpine L N r x (i + 1) := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm (i + 1)
  have hwri : w ∈ rtransSpine L N r x i := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact nextMarkMemRTransSpine L hL hgn hta hm i
  have hwpow : (nextEl (rtransSpine L N r x (i + 1)))^[indexf
      (ztransSpine L N r x i) w f] (ztransSpine L N r x i) = w := by
    rw [hpowt]
    exact indexfN hzif hwf hfnd
  have hiwrt : indexf (ztransSpine L N r x i) w (rtransSpine L N r x (i + 1))
      = indexf (ztransSpine L N r x i) w f :=
    nextElnIndexf hzirt hwrt hrtnd hwpow (by omega)
  have hziri : ztransSpine L N r x i ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hfi
  have hzz : indexf (ztransSpine L N r x i) (ztransSpine L N r x i)
      (rtransSpine L N r x i) = 0 := indexfRefl hziri
  have hTw := transIndexfSucSpine L hL hta hgn hunL hm i hfi hwri hziri
    hwrt hzirt (by omega)
  -- d ∈ r₁：n < z→w f 支由 _new 件反证；n = z→w f 支 d = w
  have hdri : d ∈ rtransSpine L N r x i := by
    rcases Nat.lt_or_eq_of_le hn with hlt' | heq
    · by_contra hnot
      have hwd : indexf w d f = n + indexf w (ztransSpine L N r x i) f := by
        refine nextElnIndexf hwf hdf hfnd ?_ (by omega)
        rw [Function.iterate_add_apply, hzn]
        exact hd.symm
      have h := (indexfInRtransSucNotRtransNewSpine L hL hta hgn hunL hm i hfi
        hfind hw hdrt hnot).1
      omega
    · have hdw : d = w := by
        rw [hd, heq]
        exact indexfN hzif hwf hfnd
      rw [hdw]
      exact hwri
  have hTd := transIndexfSucSpine L hL hta hgn hunL hm i hfi hdri hziri
    hdrt hzirt (by omega)
  obtain ⟨hW1, -⟩ := wBetwnZtransYtran0Spine L hL hta hgn hunL hm i hfi hfind hw
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

/-- **HOL `Kbwpbhq.CASES2`**（KBWPBHQ.hl:935-1069）HOL 逐字形
（PRE t ↦ t − 1）：`0 < t ∧ transform_count = t ∧
n ≤ indexf (ztrans (PRE t)) w f ⇒
(next_el r)^n (ztrans (PRE t)) = (next_el f)^n (ztrans (PRE t))`。
证 = t = i + 1 换元 + `cases2SpineAux`。 -/
theorem cases2Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {t : ℕ} (ht0 : 0 < t) (ht : transformCountSpine L N r x = t) {n : ℕ}
    (hn : n ≤ indexf (ztransSpine L N r x (t - 1)) w f) :
    (nextEl r)^[n] (ztransSpine L N r x (t - 1))
      = (nextEl f)^[n] (ztransSpine L N r x (t - 1)) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.pos_iff_ne_zero.mp ht0)
  rw [Nat.add_sub_cancel] at hn ⊢
  exact cases2SpineAux L hL hta hgn hunL hm i ht hfind hw hn

/-! ## §3 next_el_const_betwn_ztran_w_suc（KBWPBHQ.hl:1072-1110） -/

/-- **HOL `Kbwpbhq.next_el_const_betwn_ztran_w_suc`**（KBWPBHQ.hl:1072-1110）
HOL 逐字形（PRE t ↦ t − 1）：`MEM d f ∧ 0 < t ∧ transform_count = t ∧
indexf w (ztrans (PRE t)) f ≤ indexf w d f ⇒ next_el r d = f_list L d`。
证 = indexf_add_left[w;z;d;f] + indexf_antisym + indexf_lt_sizel 界算术
（z→d f < z→w f）+ CASES2 双实例（n := z→d f 与 n+1）+ indexf_n +
同面等表 congr + fListPowEqNextElPow@1。 -/
theorem nextElConstBetwnZtranWSucSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {t : ℕ} (ht0 : 0 < t) (ht : transformCountSpine L N r x = t)
    {d : ℕ × ℕ} (hd : d ∈ f)
    (hle : indexf w (ztransSpine L N r x (t - 1)) f ≤ indexf w d f) :
    nextEl r d = fList L d := by
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
  have hlt : indexf w (ytransSpine L N r x (t - 1)) f
      < indexf w (ztransSpine L N r x (t - 1)) f := hlt0
  have hwne : w ≠ ztransSpine L N r x (t - 1) := by
    intro h
    have h0 : indexf w (ztransSpine L N r x (t - 1)) f = 0 := by
      rw [h]
      exact indexfRefl hzif
    omega
  -- 界算术：z→d f < z→w f
  have hA := indexfAddLeft hwf hzif hd hle
  have hanti := indexfAntisym hwf hzif hwne
  have hwdlt := indexfLtSizel hwf hd
  have hdn : (nextEl f)^[indexf (ztransSpine L N r x (t - 1)) d f]
      (ztransSpine L N r x (t - 1)) = d := indexfN hzif hd hfnd
  have h1 := cases2Spine L hL hta hgn hunL hm hfind hw ht0 ht
    (n := indexf (ztransSpine L N r x (t - 1)) d f) (by omega)
  have h2 := cases2Spine L hL hta hgn hunL hm hfind hw ht0 ht
    (n := indexf (ztransSpine L N r x (t - 1)) d f + 1) (by omega)
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
#print axioms Kepler.Text.TameSpine.inRtransSucNotRtransNewSpine
#print axioms Kepler.Text.TameSpine.indexfInRtransSucNotRtransNewSpine
#print axioms Kepler.Text.TameSpine.cases2SpineAux
#print axioms Kepler.Text.TameSpine.cases2Spine
#print axioms Kepler.Text.TameSpine.nextElConstBetwnZtranWSucSpine
