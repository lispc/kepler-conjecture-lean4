/-
  Kepler.Text.Reduction1W1f — J4 Wave W1 批 5b 桥件（编排者按车道 v3 侦察
  收敛包施工，2026-11-10）：
  `listPairsIsNextElem`：`(v,w) ∈ listPairs l ↔ is_nextElem l v w`
  ——批 5b 的**单缺件**（车道两轮侦察收敛：其余每一环都已在库——
  `neighbors_edges` InvariantsC:848 / `is_nextElem_edges_eq` FaceDivisionProps2:456 /
  `nextElem_suc2` :461 / `Face.edges` def 体）。

  路线注记：**零假设桥**——`listPairs l = l.zip (l.drop 1 ++ l.take 1)` 的 zip 对
  恰是「连续对 ∪ 回卷对」，与 `is_nextElem` 的两析取支（连续子列 / last→head）
  逐位对齐；不需要 Nodup。配套私件：`getElemBangH`（界内 getElem! = getElem，
  TameList19 `listPairsGetElemD` 三证元形状同款）、`listPairsLengthT`、
  `listPairsGetElemT`。

  **纪律**：零公理、零占位证明、零反射式判定。
-/
import Kepler.Assembly.GoodListDefs
import Kepler.Graphs.FaceDivisionProps1
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (listPairs)
open Kepler.Graphs (is_nextElem is_sublist)

/-! ## §1 zip 引擎私件 -/

/-- 界内 `getElem!` 与 `getElem` 逐点相等（泛型）。 -/
private theorem getElemBangH {α : Type} [Inhabited α] {l : List α} {i : ℕ}
    (h : i < l.length) : l[i]! = l[i]'h := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp

/-- 同表 getElem 换证明（证明 arg 是 Prop，证不可区分）。 -/
private theorem getElemCongrList {α : Type} {l₁ l₂ : List α} (h : l₁ = l₂) {j : ℕ}
    (h₁ : j < l₁.length) (h₂ : j < l₂.length) : l₁[j]'h₁ = l₂[j]'h₂ := by
  subst h; rfl

/-- `listPairs l` 的长度 = `l` 的长度。 -/
private theorem listPairsLengthT {α : Type} (l : List α) :
    (listPairs l).length = l.length := by
  simp only [listPairs, List.length_zip, List.length_append, List.length_drop,
    List.length_take]
  omega

/-- zip 位次取值（TameList19 `listPairsGetElemD` 三证元形状，泛型重推导；
路线 = `la7_rotOne_eq`（TameLp 公开）+ `la7_getElem_rotOne`，免 drop/take
位次的从属证明搬运）。 -/
private theorem listPairsGetElemT {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    [Inhabited α] {l : List α} {j : ℕ} (hj : j < l.length)
    (hm : (j + 1) % l.length < l.length) :
    (listPairs l)[j]'(by rw [listPairsLengthT]; exact hj) =
      (l[j]'hj, l[(j + 1) % l.length]'hm) := by
  have hpos : 0 < l.length := by omega
  have hjt : j < (l.drop 1 ++ l.take 1).length := by
    rw [List.length_append, List.length_drop, List.length_take]; omega
  have hd1 : (l.drop 1 ++ l.take 1)[j]'hjt = l[(j + 1) % l.length]'hm := by
    rcases Nat.lt_or_ge j (l.length - 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt (by omega : j + 1 < l.length)] at hm
      rw [List.getElem_append_left (by rw [List.length_drop]; omega),
        List.getElem_drop]
      simp [Nat.add_comm, Nat.mod_eq_of_lt hm]
    · have hjn : j = l.length - 1 := by omega
      subst hjn
      rw [Nat.sub_add_cancel (by omega), Nat.mod_self] at hm
      rw [List.getElem_append_right (by rw [List.length_drop])]
      simp only [List.length_drop, Nat.sub_self, List.getElem_take]
      rw [← getElemBangH (Nat.mod_lt _ (by omega : 0 < l.length)),
        show (l.length - 1 + 1) % l.length = 0 from by
          rw [Nat.sub_add_cancel (by omega), Nat.mod_self],
        ← getElemBangH (by omega : 0 < l.length)]
  simp only [listPairs, List.getElem_zip]
  exact congrArg₂ _ rfl hd1

/-! ## §2 主桥 -/

/-- **批 5b 单缺件**（编排者亲作）：`(v,w) ∈ listPairs l ↔ is_nextElem l v w`。
zip 对 = 连续对 ∪ 回卷对；`is_sublist [v,w] l` ⇔ 连续对；第二析取支 ⇔ 回卷对。
零假设（无需 Nodup）。 -/
theorem listPairsIsNextElem {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    [Inhabited α] (l : List α) (v w : α) :
    (v, w) ∈ listPairs l ↔ is_nextElem l v w := by
  constructor
  · intro h
    obtain ⟨i, hi, hd⟩ := List.mem_iff_getElem.mp h
    have hjl : i < l.length := by have := listPairsLengthT l; omega
    have hmod : (i + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
    rw [listPairsGetElemT hjl hmod] at hd
    have hv : v = l[i]'hjl := congrArg Prod.fst hd.symm
    have hw : w = l[(i + 1) % l.length]'hmod := congrArg Prod.snd hd.symm
    rw [hv, hw]
    simp only [is_nextElem, is_sublist]
    rcases Nat.lt_or_ge i (l.length - 1) with hlt | hge
    · have hme : i + 1 < l.length := by omega
      have hmz : (i + 1) % l.length = i + 1 := Nat.mod_eq_of_lt hme
      have hsel : l[(i + 1) % l.length]'hmod = l[i + 1]'hme := by
        rw [← getElemBangH hmod, ← getElemBangH hme, hmz]
      refine Or.inl ⟨l.take i, l.drop (i + 2), ?_⟩
      simp only [hmz]
      conv_lhs => rw [← List.take_append_drop i l]
      rw [List.drop_eq_getElem_cons hjl, List.drop_eq_getElem_cons hme,
        show i + 1 + 1 = i + 2 from by omega, List.append_assoc]
      rfl
    · have hi1 : i = l.length - 1 := by omega
      have hpos : 0 < l.length := by omega
      have hzz : (i + 1) % l.length = 0 := by
        rw [hi1, Nat.sub_add_cancel (by omega), Nat.mod_self]
      have hsel0 : l[(i + 1) % l.length]'hmod = l[0]'hpos := by
        simp only [hzz]
      have hne' : l ≠ [] := by rintro rfl; simp at hjl
      refine Or.inr ⟨hne', ?_, ?_⟩
      · rw [List.getLast!_eq_getElem!, ← hi1, getElemBangH hjl]
      · rw [List.head!_eq_getElem!, getElemBangH hpos]
        exact hsel0
  · intro h
    rcases h with ⟨as, bs, hlab⟩ | ⟨hne, hv, hw⟩
    · have hlen2 : l.length = as.length + 2 + bs.length := by
        rw [hlab]; simp; omega
      have hile : as.length < l.length := by omega
      have hile1 : as.length + 1 < l.length := by omega
      have hle : as.length < (listPairs l).length := by
        rw [listPairsLengthT]; omega
      have hmod : (as.length + 1) % l.length < l.length :=
        Nat.mod_lt _ (by omega)
      have hpos : 0 < ([v, w] ++ bs).length := by simp
      have h0 : (as ++ [v, w] ++ bs)[as.length]'(by
          rw [← hlab]; exact hile) = v := by
        rw [List.getElem_append_left
          (by rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega)]
        simp
      have h1 : (as ++ [v, w] ++ bs)[as.length + 1]'(by
          rw [← hlab]; exact hile1) = w := by
        rw [List.getElem_append_left
          (by rw [List.length_append]; simp only [List.length_cons, List.length_nil]; omega)]
        simp
      simp only [← hlab] at h0 h1
      exact List.mem_iff_getElem.mpr ⟨as.length, hle, by
        rw [listPairsGetElemT hile hmod]
        simp only [show (as.length + 1) % l.length = as.length + 1 from
          Nat.mod_eq_of_lt hile1]
        exact Prod.ext h0 h1⟩
    · have hpos : 0 < l.length := List.length_pos_iff.mpr hne
      have him : l.length - 1 < l.length := by omega
      have hle : l.length - 1 < (listPairs l).length := by
        rw [listPairsLengthT]; omega
      have hmp : (l.length - 1 + 1) % l.length < l.length := Nat.mod_lt _ hpos
      have hsc : l.length - 1 + 1 = l.length := Nat.sub_add_cancel (by omega)
      have hmd : l.length % l.length = 0 := Nat.mod_self l.length
      exact List.mem_iff_getElem.mpr ⟨l.length - 1, hle, by
        rw [listPairsGetElemT him hmp]
        simp only [hsc, hmd]
        rw [← getElemBangH him, ← getElemBangH hpos,
          ← List.getLast!_eq_getElem!, ← List.head!_eq_getElem!]
        exact Prod.ext hv.symm hw.symm⟩

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction1.listPairsIsNextElem
