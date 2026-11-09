/-
  JcajyduAqLeaf13W1b — AQ13 叶 W1b：HOL ⑭ `betwn_in_s_list_suc`。
  路线 B 配方（DELIVERY_W1 §2）：W 元取位（`indexfBetwnEq` + `indexfN`）+
  `nextEl f → fList` 幂桥 + 见证 `l'm + i + 1`；下界由 W1
  `aq13w1_lmLtRtrans` 供给。HOL ⑭ = AQ13.hl:898-940（43 行）。
  纪律：零 axiom/sorry/admit/native_decide；主仓 tracked 零改动。
-/
import Kepler.Text.TameSpine.JcajyduAqLeaf13W1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList dart_in_face findFaceDarts_nodup)

/-- f-orbit 上 `nextEl f = fList`：`z ∈ f ⇒ (nextEl f)^[n] z = (fList)^[n] z`。 -/
private theorem aq13w1b_iterate_nextEl_f_eq_fList (L : fgraph ℕ) (hL : GoodList L)
    {x z : ℕ × ℕ} (hz : z ∈ findFaceDarts L x) (n : ℕ) :
    (nextEl (findFaceDarts L x))^[n] z = (fList L)^[n] z := by
  induction n generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hz' : (nextEl (findFaceDarts L x))^[k] z ∈ findFaceDarts L x :=
      memPowerNextEl hz k
    have hiz : (nextEl (findFaceDarts L x))^[k] z = (fList L)^[k] z := ih hz
    rw [hiz]
    have hzf : (fList L)^[k] z ∈ findFaceDarts L x := by
      rw [← hiz]; exact hz'
    have hface : findFaceDarts L ((fList L)^[k] z) = findFaceDarts L x :=
      aq10_memFindFaceImpFacesEq hL.1 hzf
    simp only [fList, hface]

/-- **HOL ⑭ `betwn_in_s_list_suc`**（AQ13.hl:898-940）：
`d ∈ betwn f l'y l'z ⇒ d ∈ s_list (rtrans … 1) x`。 -/
theorem aq13w1b_betwnMemSListRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hnf : ¬finalListSpine L (rtransSpine L N r x 1)) {d : ℕ × ℕ}
    (hd : d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)) :
    d ∈ sListSpine L (rtransSpine L N r x 1) x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hpp := pplhuljV0 L hL hgn hunL hm hf
  have hyf : lYSpine L r x ∈ findFaceDarts L x := hpp.1
  have hzf : lZSpine L N r x ∈ findFaceDarts L x := hpp.2.1
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hdf : d ∈ findFaceDarts L x := betwnMem hd
  have hidxbetw := (indexfBetwnEq hyz hfnd hyf hzf).mp hd
  set i := indexf (lYSpine L r x) d (findFaceDarts L x) - 1 with hidef
  have hpos : 0 < indexf (lYSpine L r x) d (findFaceDarts L x) := hidxbetw.1
  have hilt : indexf (lYSpine L r x) d (findFaceDarts L x)
      < indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L x) := hidxbetw.2
  have hi1 : i + 1 = indexf (lYSpine L r x) d (findFaceDarts L x) := by omega
  have hlenW : (between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)).length
      = indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L x) - 1 :=
    sizeBetwn hfnd hyf hzf hyz
  have hiW : i < (between (findFaceDarts L x) (lYSpine L r x)
      (lZSpine L N r x)).length := by omega
  have hiter : (nextEl (findFaceDarts L x))^[i + 1] (lYSpine L r x) = d := by
    rw [hi1]
    exact indexfN hyf hdf hfnd
  have hfl : (nextEl (findFaceDarts L x))^[i + 1] (lYSpine L r x)
      = (fList L)^[i + 1] (lYSpine L r x) :=
    aq13w1b_iterate_nextEl_f_eq_fList L hL hyf (i + 1)
  refine List.mem_map.mpr ⟨lMSpine L r x + i + 1, ?_, ?_⟩
  · rw [List.mem_range]
    have hlb := aq13w1_lmLtRtrans L hL hgn hm hf hnf
    omega
  · rw [← hiter, hfl]
    rw [lYSpine]
    rw [← Function.iterate_add_apply (fList L) (i + 1) (lMSpine L r x + 1) x]
    rw [show lMSpine L r x + i + 1 + 1 = (i + 1) + (lMSpine L r x + 1) by omega]

/-! 公理审计锚（编译即执行；预期标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.TameSpine.aq13w1b_betwnMemSListRtrans
