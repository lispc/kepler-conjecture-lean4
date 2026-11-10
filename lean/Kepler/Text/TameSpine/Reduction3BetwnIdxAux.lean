/-
  Kepler.Text.TameSpine.Reduction3BetwnIdxAux — 破环件 `betwnLastIdx`
  （FREEZE v2 修法 B ②′）：`e ∈ between s a b ∧ nextEl s e ∈ between s a b ⇒
  (between s a b).idxOf (nextEl s e) = (between s a b).idxOf e + 1`。

  路线：末位之前走 B2d `betwnSuccGetElem`；末位支用 **`betwnPosEnd`**
  （`φ(|B|) = idxOf b`：线性支 = idxOf b、wrap 支 = L+idxOf b 取模）
  ⇒ `nextEl s e = b`，与 `notBetwn2` 矛盾。

  纪律：零禁词；主仓双零写入。
-/
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2d

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (between)
open Kepler.Assembly (nextEl)
open Kepler.Text.TameLp (getElem_idxOf getD_eq_getElem_of_lt nextEl_eq_getD)

/-- `(m % len + 1) % len = (m + 1) % len`（B2d `modSuccEqW` 私件同证重推导）。 -/
private theorem modSuccEqAux (m len : ℕ) : (m % len + 1) % len = (m + 1) % len := by
  have h : m + 1 = len * (m / len) + (m % len + 1) := by
    have := Nat.div_add_mod m len
    omega
  rw [h, Nat.add_comm (len * (m / len)), Nat.add_mul_mod_self_left]

/-- **弧末位之后的 s-位次**：`φ(|between s a b|) = idxOf b`
（线性支 = idxOf b；wrap 支 = L + idxOf b 取模）。 -/
private theorem betwnPosEnd {α : Type} [BEq α] [LawfulBEq α] {s : List α} {a b : α}
    (hne : a ≠ b) (hnd : s.Nodup) (ha : a ∈ s) (hb : b ∈ s) :
    (s.idxOf a + 1 + (between s a b).length) % s.length = s.idxOf b := by
  have hsize := sizeBetwn hnd ha hb hne
  have hltb : s.idxOf b < s.length := List.idxOf_lt_length_iff.mpr hb
  have hidxa : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr ha
  rw [hsize, indexfCond ha hb]
  have hne2 : s.idxOf a ≠ s.idxOf b := fun heq =>
    hne ((List.idxOf_inj ha).mp heq)
  split
  · rename_i h1
    have hnum : s.idxOf a + 1 + (s.idxOf b - s.idxOf a - 1) = s.idxOf b := by omega
    rw [hnum, Nat.mod_eq_of_lt hltb]
  · rename_i h1
    have hnum : s.idxOf a + 1 + (s.idxOf b + (s.length - s.idxOf a) - 1)
        = s.length + s.idxOf b := by omega
    rw [hnum, Nat.add_comm (s.length) (s.idxOf b), Nat.add_mod_right,
      Nat.mod_eq_of_lt hltb]

/-- **破环件（B-内后继步进）**：`e` 与 `nextEl s e` 都在弧内 ⇒
`B.idxOf (nextEl s e) = B.idxOf e + 1`（差 1 与 `i+1 < |B|` 同时成立）。 -/
theorem betwnLastIdx {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {a b e : α} (hne : a ≠ b) (hnd : s.Nodup) (ha : a ∈ s) (hb : b ∈ s)
    (he : e ∈ between s a b) (hs : nextEl s e ∈ between s a b) :
    (between s a b).idxOf (nextEl s e) = (between s a b).idxOf e + 1 := by
  have hBnd : (between s a b).Nodup := uniqBetwn hnd ha hb hne
  have hBpos : 0 < (between s a b).length := List.length_pos_of_mem he
  have hi : (between s a b).idxOf e < (between s a b).length :=
    List.idxOf_lt_length_iff.mpr he
  by_cases hcase : (between s a b).idxOf e + 1 < (between s a b).length
  · -- 末位之前：B2d betwnSuccGetElem 直给
    have hBe : (between s a b)[(between s a b).idxOf e] = e := getElem_idxOf he
    have hstep := betwnSuccGetElem hne hnd ha hb hcase (by rw [hBe]; exact hs)
    have hBe' : nextEl s ((between s a b)[(between s a b).idxOf e]'(by omega))
        = nextEl s e := congrArg (nextEl s) hBe
    rw [← hBe', hstep]
    exact hBnd.idxOf_getElem ((between s a b).idxOf e + 1) (by omega)
  · -- 末位：nextEl s e = b，与 notBetwn2 矛盾
    have hnb : b ∉ between s a b := notBetwn2 hnd
    have hBe : (between s a b)[(between s a b).idxOf e] = e := getElem_idxOf he
    have hpos := betwnPosGetElem hne hnd ha hb hi
    have hsidx : s.idxOf e = (s.idxOf a + (between s a b).length) % s.length := by
      have hkey : s.idxOf e
          = (s.idxOf a + 1 + (between s a b).idxOf e) % s.length := by
        conv_lhs => rw [← hBe]
        conv_lhs => rw [hpos]
        exact hnd.idxOf_getElem _
          (Nat.mod_lt _ (List.length_pos_of_mem ha))
      have hidxEq : s.idxOf a + 1 + (between s a b).idxOf e
          = s.idxOf a + (between s a b).length := by omega
      rw [hkey, hidxEq]
    have hidx2 : (s.idxOf e + 1) % s.length = s.idxOf b := by
      rw [hsidx, modSuccEqAux,
        show s.idxOf a + (between s a b).length + 1
          = s.idxOf a + 1 + (between s a b).length from by omega,
        betwnPosEnd hne hnd ha hb]
    have hes : e ∈ s := Kepler.Graphs.inbetween_inset he
    have hcontra : nextEl s e = b := by
      rw [nextEl_eq_getD hes, hidx2,
        getD_eq_getElem_of_lt (List.idxOf_lt_length_iff.mpr hb),
        getElem_idxOf hb]
    exact absurd (hcontra ▸ hs) hnb

end Kepler.Text.TameSpine

-- 公理审计锚（编译即执行；预期标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.betwnPosEnd
#print axioms Kepler.Text.TameSpine.betwnLastIdx
