/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12U — AQ12 叶 W-F3b（decls 59–61）。

  HOL：AQ12.hl:3086-:3235（150 行）
  · 59 `s_list_in_betwn`（93）· 60 `s_list_in_rtrans`（22）· 61 `s_list_not_in_fst`（35）

  件目/依赖（开工报价）：3 件 / 1 文件；估 220–300（≤350）。
  依赖 55（`aqs_nextElPowerTransEqF`）与 58（`aqs_nextMarkCaseMem`）已落（12T）。
  **本波不吃 `h4`**（sList/parts/indexf 层）。DIFFERS：F2 的 40/41/45/46/51/53/54 吃。

  路线（59 的 Lean 短路线：indexf 弧论证，替代 HOL 93 行逐支不等式）：
  `d ∈ sList = (fList)^(i+1) x`（i < l'm）→ 55 给 `= (nextEl r)^i w`（w = nextEl f x）
  → `indexf w d = i < indexf w y < indexf w z < |r|` → `indexfAddLeft` 两次 +
  `indexfAntisym` 两次 → `0 < indexf z d < indexf z y` → `indexfBetwnEq` 落 between。
  60 由 59 + split.2 展开（f2 中间段）；61 由 60 + `aq1` flatten Nodup 的
  append 互斥（SND 在 replace 段、FST 在单点段）。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12T

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList nList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face)

/-- `r ∈ N ∧ d ∈ [r2] ⇒ d ∈ replaceSpine r [r2] N`（私件，与 12L/12N 同证）。 -/
private theorem aq12u_memReplaceSpineOfMem {α : Type} [DecidableEq α] {z x : α}
    {ys xs : List α} (hz : z ∈ xs) (hx : x ∈ ys) : x ∈ replaceSpine z ys xs := by
  induction xs with
  | nil => exact absurd hz (List.not_mem_nil)
  | cons a as ih =>
    by_cases haz : a = z
    · rw [replaceSpine, if_pos haz]
      exact List.mem_append.mpr (Or.inl hx)
    · rw [replaceSpine, if_neg haz]
      rcases List.mem_cons.mp hz with h | h
      · exact absurd h.symm haz
      · exact List.mem_cons_of_mem _ (ih h)

/-- **HOL `s_list_in_betwn`**（AQ12.hl:3086-:3178）：`d ∈ sList ⇒ d ∈ betwn r z y`。 -/
theorem aqs_sListInBetwn (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {z y z1 : ℕ × ℕ} (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y)
    (hz1 : prevEl r z = z1) {d : ℕ × ℕ} (hd : d ∈ sListSpine L r x) :
    d ∈ between r z y := by
  obtain ⟨i, hi, hie⟩ := List.mem_map.mp hd
  rw [List.mem_range] at hi
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hwr : nextEl (findFaceDarts L x) x ∈ r := aq10_nextMarkMemRTrans L hL hgn hm
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hiy : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r = lMSpine L r x :=
    aq10_indexfYtransEqLm1 L hL hgn hm hf
  have hiy_lt_hiz : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r
      < indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) r :=
    aq10_indexfYLeZInR0 L hL hgn hm hf
  have hiz_lt_len : indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) r
      < r.length := indexfLtSizel hwr hzr
  have hi_lt_iy : i < indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r := by
    rw [hiy]; exact hi
  have hxd : x ∈ listOfDarts L := normalListListOfDarts hm.1.2.1 x
    (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  -- d = (nextEl r)^i w
  have hpow := aqs_nextElPowerTransEqF L hL hgn hm hf
    (w := nextEl (findFaceDarts L x) x) rfl (le_of_lt hi_lt_iy)
  have hd_eq : (nextEl r)^[i] (nextEl (findFaceDarts L x) x) = d := by
    rw [hpow]
    calc (nextEl (findFaceDarts L x))^[i] ((nextEl (findFaceDarts L x)) x)
        = (nextEl (findFaceDarts L x))^[i + 1] x :=
          (Function.iterate_succ_apply (nextEl (findFaceDarts L x)) i x).symm
      _ = (fList L)^[i + 1] x := (fListPowEqNextElPow L hL x hxx (i + 1)).symm
      _ = d := hie
  have hdr : d ∈ r := by
    rw [← hd_eq]
    exact memPowerNextEl hwr i
  have hdw : indexf (nextEl (findFaceDarts L x) x) d r = i := by
    rw [← hd_eq]
    exact nextElnIndexf hwr (memPowerNextEl hwr i) hrnd rfl
      (lt_trans hi_lt_iy (lt_trans hiy_lt_hiz hiz_lt_len))
  -- 弧上的线性加法律
  have hadd_y : i + indexf d (lYSpine L r x) r
      = indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r := by
    have h := indexfAddLeft hwr hdr hyr (le_of_lt (by rw [hdw]; exact hi_lt_iy))
    rwa [hdw] at h
  have hadd_z : i + indexf d (lZSpine L N r x) r
      = indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) r := by
    have h := indexfAddLeft hwr hdr hzr
      (le_of_lt (by rw [hdw]; exact lt_trans hi_lt_iy hiy_lt_hiz))
    rwa [hdw] at h
  have hadd_yz : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) r
      + indexf (lYSpine L r x) (lZSpine L N r x) r
      = indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) r :=
    indexfAddLeft hwr hyr hzr (le_of_lt hiy_lt_hiz)
  have hne_zd : lZSpine L N r x ≠ d := by
    intro h
    rw [← h] at hdw
    omega
  have hanti_zd : indexf (lZSpine L N r x) d r + indexf d (lZSpine L N r x) r
      = r.length := indexfAntisym hzr hdr hne_zd
  have hanti_zy : indexf (lZSpine L N r x) (lYSpine L r x) r
      + indexf (lYSpine L r x) (lZSpine L N r x) r = r.length :=
    indexfAntisym hzr hyr (Ne.symm hyz)
  have hmem : d ∈ between r (lZSpine L N r x) (lYSpine L r x) :=
    (indexfBetwnEq (Ne.symm hyz) hrnd hzr hyr).mpr
      ⟨by omega, by omega⟩
  rw [← hz, ← hy]
  exact hmem

/-- **HOL `s_list_in_rtrans`**（AQ12.hl:3179-:3200）：`d ∈ sList ⇒ d ∈ SND split`。 -/
theorem aqs_sListInRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y)
    (hz1 : prevEl r z = z1)
    (hfind : findFaceDarts L x = f) {d : ℕ × ℕ}
    (hd : d ∈ sListSpine L r x) :
    d ∈ (splitNormalListSpine L r f y z1).2 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hb : d ∈ between r (lZSpine L N r x) (lYSpine L r x) :=
    aqs_sListInBetwn L hL hgn hm hf rfl rfl rfl hd
  have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r f y z1 := by
    rw [← hfindcanon, ← hy, ← hz1c]
  have hSND : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2
      = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x])
        ++ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
            (lZSpine L N r x) := by
    simp only [splitNormalListSpine]
    rw [nextElPrevElUniq hrnd _]
  have hmem : d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
    rw [hSND]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr hb)))))
  rw [← hsplit_eq]
  exact hmem

/-- **HOL `s_list_not_in_fst`**（AQ12.hl:3201-:3235）：`d ∈ sList ⇒ d ∉ FST split`。 -/
theorem aqs_sListNotInFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (f : List (ℕ × ℕ))
    {z y z1 : ℕ × ℕ} (hz : lZSpine L N r x = z) (hy : lYSpine L r x = y)
    (hz1 : prevEl r z = z1)
    (hfind : findFaceDarts L x = f) {d : ℕ × ℕ}
    (hd : d ∈ sListSpine L r x) :
    d ∉ (splitNormalListSpine L r f y z1).1 := by
  intro hdF
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hdS := aqs_sListInRtrans L hL hgn hm hf f hz hy hz1 hfind hd
  have hz1c : prevEl r (lZSpine L N r x) = z1 := by rw [hz]; exact hz1
  have hfindcanon : findFaceDarts L (lYSpine L r x) = f :=
    (aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hf).1).trans hfind
  have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x)))
      = splitNormalListSpine L r f y z1 := by
    rw [← hfindcanon, ← hy, ← hz1c]
  -- ntrans 1 = replace r [S] N ++ [F]（f-split 字面）
  have hnt : ntransSpine L N r x 1
      = replaceSpine r [(splitNormalListSpine L r f y z1).2] N
        ++ [(splitNormalListSpine L r f y z1).1] := by
    rw [ntrans1 L N r x hf, ← hsplit_eq]
  have hflat : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  rw [hnt] at hflat
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil] at hflat
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hflat
  have hS_mem : (splitNormalListSpine L r f y z1).2
      ∈ replaceSpine r [(splitNormalListSpine L r f y z1).2] N :=
    aq12u_memReplaceSpineOfMem hm.1.2.2.1 (List.mem_singleton_self _)
  have hdA : d ∈ (replaceSpine r [(splitNormalListSpine L r f y z1).2] N).flatten :=
    List.mem_flatten.mpr ⟨_, hS_mem, hdS⟩
  have hdB : d ∈ (splitNormalListSpine L r f y z1).1 ++ [] :=
    List.mem_append.mpr (Or.inl hdF)
  exact hdisj d hdA d hdB rfl

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_sListInBetwn
#print axioms Kepler.Text.TameSpine.aqs_sListInRtrans
#print axioms Kepler.Text.TameSpine.aqs_sListNotInFst
