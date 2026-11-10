/-
  Kepler.Text.TameSpine.Reduction3Obdatyb — tame-corr nb8：OBDATYB 章全件
  （EXSITS_MEM_LE_COUNT + OBDATYB；J4 `hOb` 槽上游，余量段）。

  ┌─ 归属对账（HOL → spine 形）───────────────────────────────────
  │ ① `obdatybFinalSpine`（OBDATYB 证体 OBDATYB.hl:131-144 的 final 支，
  │    单列为件，前提只取 marked_list 的前 7 合取 `MarkedListSpine`）：
  │    final_list L r ∧ MEM d (find_face L x) ⇒ MEM d r。
  │    证 = indexf_n（f 上）+ final_list_power + 幂成员。锚点取 x 而非
  │    HOL 的 w = next_el f x：同一 final_list_power 事实，免一次同面
  │    congr（记档：路线等价、非逐 tactic）。单列理由：链世界形在
  │    final 态拿不到 hs 槽（`MarkedListSpineFull` 不可得），但核 7 合取
  │    经 markedListCore_iff_markedListSpine 无条件可得。
  │ ② `exsitsMemLeCountSpine`（OBDATYB.hl:35-112 EXSITS_MEM_LE_COUNT）：
  │    MEM d f ∧ MEM d (flatten N) ∧ transform_count = t ⇒
  │    ∀ i, indexf w d f ≤ indexf w (l'y(i)) f ∧ i < t ⇒ MEM d r。
  │    证（HOL 同构，对 i 归纳）：零支 properties_of_ytrans0@0 (1) +
  │    next_el_power_trans_eq_f@0 + MEM_POWER_NEXT_EL；步支 ≤ 支 IH，
  │    > 支二分——not_in_ntrans_i + DANGEYJ 反证 / QCDVKEA +
  │    indexf_add_left×2 + betwn_ztran_ytrans_suc_const（nb7）+ PNXVWFS2
  │    （nb7）+ MEM_POWER_NEXT_EL。
  │ ③ `obdatybSpine`（OBDATYB.hl:113-190 **OBDATYB**）：
  │    MEM d (find_face L x) ∧ MEM d (flatten N) ⇒ MEM d r。
  │    证（HOL 同构）：transform_count = 0 支 final_list_transform_count
  │    + ①；> 0 支对 indexf w d f 与 indexf w (l'y(t−1)) f 二分——
  │    ≤ 支 ②；> 支二分 not_in_ntrans_i + DANGEYJ 反证 /
  │    indexf_add_left + indexf_antisym 界 + CASES2（nb8）+ PNXVWFS2 +
  │    MEM_POWER_NEXT_EL（w = z 支与 PPLHULJ 矛盾）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpine / MarkedListSpineFull）；
  │ 消费件（aqiunpp3 / normalListUniqNonnil / normalListListOfDarts /
  │ finalListPower / transformCountSpineNot / finalListTransformCountSpine
  │ / propertiesOfYtrans0Spine / nextElPowerTransEqFSpine /
  │ nextMarkMemRTransSpine / pplhuljV0 / qcdvkeaTowerSpine / notInNtrans /
  │ DANGEYJ / betwnZtranYtransSucConstSpine / cases2Spine / pnxvwfs2Spine
  │ / aq10_memNextMarkInface / TameList3 indexf 族 / memPowerNextEl /
  │ TameLp 面件）同世界零混合；零 Dart 载体件。默认心跳、linter 全开。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqCases2

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup dart_in_face)

/-! ## §1 OBDATYB 的 final 支（OBDATYB.hl:131-144） -/

/-- **OBDATYB 的 final 支**（HOL OBDATYB.hl:131-144；前提只取 marked_list
前 7 合取 `MarkedListSpine`）：`final_list L r ∧ MEM d (find_face L x) ⇒
MEM d r`。证 = indexf_n（f 上，锚 x）+ final_list_power（r 幂 = 面幂，
且幂不出 r）。 -/
theorem obdatybFinalSpine (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hmc : MarkedListSpine hL N r x) (hfin : finalListSpine L r)
    {d : ℕ × ℕ} (hdf : d ∈ findFaceDarts L x) : d ∈ r := by
  have hxr : x ∈ r := hmc.2.2.2.1
  have hrnd : r.Nodup := (normalListUniqNonnil hmc.2.1 hmc.2.2.1).1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hmc.2.1 x (List.mem_flatten.mpr ⟨r, hmc.2.2.1, hxr⟩)
  have hxf : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hdn := indexfN hxf hdf hfnd
  obtain ⟨hmem, -, heq⟩ :=
    finalListPower hL hfin hxr hrnd hxd (indexf x d (findFaceDarts L x))
  rw [heq, hdn] at hmem
  exact hmem

/-! ## §2 EXSITS_MEM_LE_COUNT（OBDATYB.hl:35-112） -/

/-- **HOL `Obdatyb.EXSITS_MEM_LE_COUNT`**（OBDATYB.hl:35-112）：
`MEM d f ∧ MEM d (flatten N) ∧ transform_count = t ⇒
∀ i, indexf w d f ≤ indexf w (l'y(i)) f ∧ i < t ⇒ MEM d r`。
证（HOL 同构，对 i 归纳；详见文件头 ②）。 -/
theorem exsitsMemLeCountSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {t : ℕ} (ht : transformCountSpine L N r x = t)
    {d : ℕ × ℕ} (hdf : d ∈ f) (hdN : d ∈ N.flatten) :
    ∀ i, indexf w d f ≤ indexf w (ytransSpine L N r x i) f ∧ i < t →
      d ∈ r := by
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  have hwr : w ∈ r := by
    have h := nextMarkMemRTransSpine L hL hgn hta hm 0
    rw [show rtransSpine L N r x 0 = r from rfl, hfind, hw] at h
    exact h
  intro i
  induction i with
  | zero =>
    rintro ⟨h1, h2⟩
    have hf0 : ¬ finalListSpine L (rtransSpine L N r x 0) :=
      transformCountSpineNot L N r x (by omega)
    obtain ⟨hP1, -, -, -⟩ :=
      propertiesOfYtrans0Spine L hL hta hgn hunL hm 0 hfind hw hf0
    have hdn := indexfN hwf hdf hfnd
    have hb : indexf w d f ≤ indexf w (ytransSpine L N r x 0)
        (rtransSpine L N r x 0) := by omega
    have hp := nextElPowerTransEqFSpine L hL hta hgn hm 0 hf0 hfind hw
      (n := indexf w d f) hb
    rw [show rtransSpine L N r x 0 = r from rfl, hfind, hdn] at hp
    have h := memPowerNextEl hwr (indexf w d f)
    rw [hp] at h
    exact h
  | succ i ih =>
    rintro ⟨h1, h2⟩
    by_cases hle : indexf w d f ≤ indexf w (ytransSpine L N r x i) f
    · exact ih ⟨hle, by omega⟩
    · have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
        transformCountSpineNot L N r x (by omega)
      have hfs : ¬ finalListSpine L (rtransSpine L N r x (i + 1)) :=
        transformCountSpineNot L N r x (by omega)
      have hmr := aqiunpp3 L hL i hta hgn hm
      obtain ⟨-, hzf0, -⟩ := pplhuljV0 L hL hgn hunL hmr hfi
      rw [hfind] at hzf0
      have hzif : ztransSpine L N r x i ∈ f := hzf0
      have hQ := qcdvkeaTowerSpine L hL hta hgn hm i hfs hfind hw
      by_cases hc : indexf w d f < indexf w (ztransSpine L N r x i) f
      · -- 窗口支：not_in_ntrans_i + DANGEYJ 与 d ∈ flatten N 矛盾
        exfalso
        have hnt := notInNtrans L hL hta hgn hunL hm hfind hw hfi hc
          (by omega) hdf
        have hsub := DANGEYJ L hL hta hgn N r x 0 i hm (Nat.zero_le i)
        have hdN0 : d ∈ (ntransSpine L N r x 0).flatten := hdN
        exact hnt (hsub hdN0)
      · have hmr1 := aqiunpp3 L hL (i + 1) hta hgn hm
        obtain ⟨hysf0, -, -⟩ := pplhuljV0 L hL hgn hunL hmr1 hfs
        rw [hfind] at hysf0
        have hysf : ytransSpine L N r x (i + 1) ∈ f := hysf0
        have hA1 := indexfAddLeft hwf hzif hysf hQ
        have hA2 := indexfAddLeft hwf hzif hdf (by omega)
        have hdn := indexfN hzif hdf hfnd
        have hb := betwnZtranYtransSucConstSpine L hL hta hgn hunL hm i hfs
          hfind hw (n := indexf (ztransSpine L N r x i) d f) (by omega)
        rw [hdn] at hb
        have hzir : ztransSpine L N r x i ∈ r :=
          pnxvwfs2Spine L hL hta hgn hunL hm i hfi
        have h := memPowerNextEl hzir (indexf (ztransSpine L N r x i) d f)
        rw [hb] at h
        exact h

/-! ## §3 OBDATYB（OBDATYB.hl:113-190） -/

/-- **HOL `Obdatyb.OBDATYB`**（OBDATYB.hl:113-190）：
`MEM d (find_face L x) ∧ MEM d (flatten N) ⇒ MEM d r`。
证（HOL 同构；详见文件头 ③）。 -/
theorem obdatybSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {d : ℕ × ℕ} (hdf : d ∈ findFaceDarts L x) (hdN : d ∈ N.flatten) :
    d ∈ r := by
  obtain ⟨t, ht⟩ : ∃ t, transformCountSpine L N r x = t := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, nextEl (findFaceDarts L x) x = w := ⟨_, rfl⟩
  rcases Nat.eq_zero_or_pos t with ht0 | ht0
  · -- transform_count = 0：final r
    have hfin := finalListTransformCountSpine L hL hta hgn hm ht
    rw [ht0, show rtransSpine L N r x 0 = r from rfl] at hfin
    exact obdatybFinalSpine L hL hm.1 hfin hdf
  · by_cases hle : indexf w d (findFaceDarts L x)
        ≤ indexf w (ytransSpine L N r x (t - 1)) (findFaceDarts L x)
    · exact exsitsMemLeCountSpine L hL hta hgn hunL hm rfl hw ht hdf hdN
        (t - 1) ⟨hle, by omega⟩
    · have hfi : ¬ finalListSpine L (rtransSpine L N r x (t - 1)) :=
        transformCountSpineNot L N r x (by omega)
      have hmr := aqiunpp3 L hL (t - 1) hta hgn hm
      have hwf : w ∈ findFaceDarts L x := by
        rw [← hw]
        exact aq10_memNextMarkInface L hL hgn hm
      have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
      obtain ⟨-, hzf0, hlt0⟩ := pplhuljV0 L hL hgn hunL hmr hfi
      rw [hw] at hlt0
      have hzif : ztransSpine L N r x (t - 1) ∈ findFaceDarts L x := hzf0
      have hlt : indexf w (ytransSpine L N r x (t - 1)) (findFaceDarts L x)
          < indexf w (ztransSpine L N r x (t - 1)) (findFaceDarts L x) := hlt0
      by_cases hc : indexf w d (findFaceDarts L x)
          < indexf w (ztransSpine L N r x (t - 1)) (findFaceDarts L x)
      · -- 窗口支：not_in_ntrans_i + DANGEYJ 与 d ∈ flatten N 矛盾
        exfalso
        have hnt := notInNtrans L hL hta hgn hunL hm rfl hw hfi hc
          (by omega) hdf
        have hsub := DANGEYJ L hL hta hgn N r x 0 (t - 1) hm (Nat.zero_le _)
        have hdN0 : d ∈ (ntransSpine L N r x 0).flatten := hdN
        exact hnt (hsub hdN0)
      · have hwne : w ≠ ztransSpine L N r x (t - 1) := by
          intro h
          have h0 : indexf w (ztransSpine L N r x (t - 1))
              (findFaceDarts L x) = 0 := by
            rw [h]
            exact indexfRefl hzif
          omega
        have hA := indexfAddLeft hwf hzif hdf (by omega)
        have hanti := indexfAntisym hwf hzif hwne
        have hwdlt := indexfLtSizel hwf hdf
        have hdn := indexfN hzif hdf hfnd
        have hb := cases2Spine L hL hta hgn hunL hm rfl hw ht0 ht
          (n := indexf (ztransSpine L N r x (t - 1)) d (findFaceDarts L x))
          (by omega)
        rw [hdn] at hb
        have hzir : ztransSpine L N r x (t - 1) ∈ r :=
          pnxvwfs2Spine L hL hta hgn hunL hm (t - 1) hfi
        have h := memPowerNextEl hzir
          (indexf (ztransSpine L N r x (t - 1)) d (findFaceDarts L x))
        rw [hb] at h
        exact h

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.obdatybFinalSpine
#print axioms Kepler.Text.TameSpine.exsitsMemLeCountSpine
#print axioms Kepler.Text.TameSpine.obdatybSpine
