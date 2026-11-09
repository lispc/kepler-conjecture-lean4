/- JcajyduAqLeaf13W4a2c2 — AQ13 y=z1 支：lp≠z1 定位分件。0 禁词。 -/
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4a2c
import Kepler.Text.TameSpine.JcajyduAqLeaf13W4a2b
import Kepler.Text.TameSpine.JcajyduAqLeaf8W2b

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace Kepler.Text.TameSpine
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList GoodList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup)

/-- **y=z1 · `lp≠z1` 定位分件**：`p∈parts f1`、`y=LAST p`、`y≠z1` ⇒
`p∈parts r` 时 `p1.getLast!=y`；`p∉parts r` 时同样 `p1.getLast!=y`（本件直接给无条件形）。 -/
theorem aq13w4a2c2_lastOfPartOfNeLast (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {p p1 : List (ℕ × ℕ)} {y : ℕ × ℕ}
    (hp : p ∈ partsSpine L ([nextEl r (lYSpine L r x)] ++
      between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) ++
      [prevEl r (lZSpine L N r x)]))
    (hyp : y ∈ p) (hylast : y = p.getLast!)
    (hyz : y ≠ prevEl r (lZSpine L N r x))
    (hp1 : p1 ∈ partsSpine L r) (hyp1 : y ∈ p1) :
    p1.getLast! = y := by
  obtain ⟨hrnd, hrne⟩ := normalListUniqNonnil hm.1.2.1 hm.1.2.2.1
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  -- f1 Nodup / 末元
  set a := nextEl r (lYSpine L r x) with hadef
  set b := prevEl r (lZSpine L N r x) with hbdef
  have hndNt : (ntransSpine L N r x 1).flatten.Nodup := aq1 L hL N r x hgn hm
  have hsplit1 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 =
      ((((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
          (lZSpine L N r x)).map (fun d => ndSpine L d)).flatten).reverse) ++
        ([a] ++ between r a b ++ [b]) := by
    dsimp only [splitNormalListSpine]
    simp only [ndSpine]
    rw [hbdef, nextElPrevElUniq hrnd _, ← hadef, ← hbdef]
  have hf1nd : ([a] ++ between r a b ++ [b]).Nodup := by
    have h := uniqFlattenUniq _ hndNt _ (aq8w2b_fstMemRtran1 L hf)
    rw [hsplit1] at h
    exact (List.nodup_append.mp h).2.1
  have hf1ne : ([a] ++ between r a b ++ [b]) ≠ [] := by simp
  have hf1last : ([a] ++ between r a b ++ [b]).getLast! = b := by
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_append]
    simp
  have hdf1 : y ∈ ([a] ++ between r a b ++ [b]) :=
    memPartsImp L hf1nd hf1ne hp y hyp
  -- 末元支 / 断口支
  by_cases hyr : y = r.getLast!
  · exact aq13w4a2c_lastOfPartOfLast L hL hm.1.2.1 hm.1.2.2.1 hp1 hyp1 hyr
  · have hyb : y ≠ ([a] ++ between r a b ++ [b]).getLast! := by
      rw [hf1last]; exact hyz
    have hbreakF1 : ¬(nextEl ([a] ++ between r a b ++ [b]) y = fList L (eList y)) :=
      (aqs_conditionLastParts L hf1nd hf1ne hp hyp hyb).mpr hylast
    have hnext := aq13w4a2_nextEl_f1 L hL hgn hm hf (d := y) hdf1 hyz
    have hbreakR : ¬(nextEl r y = fList L (eList y)) := by
      rw [← hnext]; exact hbreakF1
    exact ((aqs_conditionLastParts L hrnd hrne hp1 hyp1 hyr).mp hbreakR).symm

#print axioms Kepler.Text.TameSpine.aq13w4a2c2_lastOfPartOfNeLast
