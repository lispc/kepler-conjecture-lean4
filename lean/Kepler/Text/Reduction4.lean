/-
  Kepler.Text.Reduction4 — J 战役 J1（reduction4.hl 移植）第一批：
  between 索引刻画层 + betwn 不相交/覆盖件 + ifbetwn 四件。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）──────
  │ 本批 = reduction4.hl（5,436 行/118 定理）依赖闭包内**最底自含切片**。
  │ reduction4.hl 本地件 4 条：
  │   mem_ifbetwn      :2746 → §D memOfMemIfbetwn
  │   ifbetwn_disjoint :3803 → §D ifbetwnDisjoint
  │   ifbetwn_cover    :3818 → §D ifbetwnCover
  │   ifbetwn_refl     :4499 → §D ifbetwnRefl
  │ 外科内联的闭包内支撑件 4 条（不另落文件；J2/J3 车道到达时吸收去重）：
  │   tame_list.hl   not_betwn1    :2574 → §C notBetwn1
  │   tame_list.hl   not_betwn2    :2600 → §C notBetwn2
  │   tame_list.hl   betwn_cases   :2744 → §C betwnMemCover
  │   reduction3.hl  betwn_disjoint :2851 → §C betwnDisjoint（J3 领土）
  │ 闭包内已有件直接消费不重落：betwn_mem（tame_list.hl:2306）↦
  │ ListAuxLemmas.inbetween_inset；getD/idxOf 泛型件 ↦ TameLp §10。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ `betwn` ↦ `Kepler.Graphs.between`（ListAux:27，[BEq α] 烘焙）；
  │ `ifbetwn` ↦ `Kepler.Text.Reduction5.ifbetwn`（Reduction5Base:216，
  │ [DecidableEq α] 烘焙，reduction4 链定义基座 W0）。
  │ 泛型 binder 只用 `[DecidableEq α]`（rx 桥车道雷区记档：附加
  │ BEq/LawfulBEq 实例与 def 烘焙失配；Lean core Core.lean:812 提供
  │ [DecidableEq α] → LawfulBEq α，故 between/splitAt/ListAuxLemmas 侧
  │ synth 唯一，全部走派生实例）。
  │ 环安全：imports = Reduction5Base + ListAuxLemmas；import 闭包零
  │ `Kepler.Assembly` 主模块、零 `Kepler.Text.TameSpine.*`
  │ （Reduction5Base 头注岛纪律）。零 axiom/sorry/admit/native_decide。
  └────────────────────────────────────────────────────────────────

  ┌─ 版本差异（DIFFERS 记档）─────────────────────────────────────
  │ ① HOL 的 betwn 位置公式（betwn_take_drop 分支形，tame_list.hl
  │   :1181 起）在本批落成 **idxOf 区间刻画形**：两条等式（
  │   between_eq_take_of_idxOf_lt / between_eq_append_of_idxOf_gt）
  │   + 四条成员往返。D 链 TameList72:205 `mem_between_iff_idx` 是
  │   BEq 岛内私件、无等式方向，本批为 Reduction5 岛独立重落。
  │ ② `betwn_disjoint` 本属 reduction3.hl（J3 领土），但被
  │   reduction4.hl:3803 直接消费 ⇒ 按依赖闭包外科内联进本批；
  │   J3 批次到达时吸收即可，勿重复落库。
  │ ③ `betwn_cases`（tame_list.hl:2744）HOL 走 indexf_antisym 路线；
  │   本批走 §A 索引刻画直接 omega，结论句逐字同形。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Base
import Kepler.Graphs.ListAuxLemmas

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4

open Kepler.Graphs (between splitAt splitAtRec between_def splitAt_dist_ram
  splitAt_no_ram splitAt_ram inbetween_inset set_between_id)
open Kepler.Text.Reduction5 (ifbetwn)
open Kepler.Text.TameLp (getElem_idxOf)

/-! ## §0 位置小件（idxOf 算术，私有） -/

section PositionAux

variable {α : Type*} [DecidableEq α]

/-- 成员位置取值：`x ∈ s` ⇒ `s[s.idxOf x] = x`（委托 TameLp §10 泛型件）。 -/
private theorem getElem_idxOf_mem {s : List α} {x : α} (hx : x ∈ s) :
    s[s.idxOf x]'(List.idxOf_lt_length_iff.mpr hx) = x := getElem_idxOf hx

/-- 同位置即同元素（`Nodup s`；getElem? 中转绕开依赖括号重写）。 -/
private theorem eq_of_idxOf_eq {s : List α} (hnd : s.Nodup) {x y : α} (hx : x ∈ s)
    (hy : y ∈ s) (h : s.idxOf x = s.idxOf y) : x = y := by
  have h1 := getElem_idxOf_mem hx
  have h2 := getElem_idxOf_mem hy
  have m1 : s[s.idxOf x]? = some x := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hx), h1]
  have m2 : s[s.idxOf y]? = some y := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hy), h2]
  rw [← h] at m2
  rw [m1] at m2
  exact Option.some.inj m2

/-- `Nodup s` 下取值定位置：`s.idxOf s[p] = p`。 -/
private theorem idxOf_getElem_of_nodup {s : List α} (hnd : s.Nodup) {p : ℕ}
    (hp : p < s.length) : s.idxOf s[p] = p := by
  induction s generalizing p with
  | nil => exact absurd hp (Nat.not_lt_zero _)
  | cons a t ih =>
    cases p with
    | zero => simp only [List.getElem_cons_zero]; exact List.idxOf_cons_self
    | succ j =>
      have hj : j < t.length := by
        have := hp
        simp only [List.length_cons] at this
        omega
      have hmem : t[j] ∈ t := List.getElem_mem hj
      have hne : a ≠ t[j] := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hmem)
      simp only [List.getElem_cons_succ, List.idxOf_cons_ne t hne]
      exact congrArg Nat.succ (ih (List.nodup_cons.mp hnd).2 hj)

/-- `Nodup s` 下位置定取值（上一件的反向）。 -/
private theorem idxOf_eq_of_getElem {s : List α} (hnd : s.Nodup) {x : α} {p : ℕ}
    (hp : p < s.length) (hx : s[p] = x) : s.idxOf x = p := by
  rw [← hx]
  exact idxOf_getElem_of_nodup hnd hp

/-- `x ∉ a` 时 `(a ++ b).idxOf x = a.length + b.idxOf x`。 -/
private theorem idxOf_append_of_not_mem {a b : List α} {x : α} (hx : x ∉ a) :
    (a ++ b).idxOf x = a.length + b.idxOf x := by
  induction a with
  | nil => simp
  | cons c t ih =>
    have hbc : (c == x) = false :=
      beq_eq_false_iff_ne.mpr (fun h => hx (by rw [← h]; exact List.mem_cons_self))
    have hxt : x ∉ t := fun h' => hx (List.mem_cons_of_mem _ h')
    simp only [List.cons_append, List.idxOf_cons, hbc, cond_false, ih hxt,
      List.length_cons]
    omega

/-- 三段分解 `s = A ++ x :: B`（`Nodup s`）的端点归属事实。 -/
private theorem split_facts {s : List α} (hnd : s.Nodup) {A B : List α} {x : α}
    (hAB : s = A ++ x :: B) :
    x ∉ A ∧ x ∉ B ∧ A.Nodup ∧ B.Nodup ∧ (∀ z ∈ A, z ∉ B) ∧ (∀ z ∈ B, z ∉ A) := by
  obtain ⟨hndA, hndXB, hdisj⟩ := List.nodup_append'.mp (hAB ▸ hnd)
  obtain ⟨hdXB, hndB⟩ := List.nodup_cons.mp hndXB
  exact ⟨fun h => hdisj (a := x) h (List.mem_cons_self (a := x) (l := B)),
    hdXB,
    hndA, hndB,
    fun z hzA hzB => hdisj (a := z) hzA (List.mem_cons_of_mem x hzB),
    fun z hzB hzA => hdisj (a := z) hzA (List.mem_cons_of_mem x hzB)⟩

/-- `s = A ++ x :: B`（Nodup）⇒ `s.idxOf x = A.length`。 -/
private theorem idxOf_self_of_split {s : List α} (hnd : s.Nodup) {A B : List α} {x : α}
    (hAB : s = A ++ x :: B) : s.idxOf x = A.length := by
  obtain ⟨hdA, _, _, _, _, _⟩ := split_facts hnd hAB
  rw [hAB, List.idxOf_append, if_neg hdA, List.idxOf_cons_self]
  omega

/-- `s = A ++ x :: B`、`y ∈ B` ⇒ `s.idxOf y = A.length + 1 + B.idxOf y`。 -/
private theorem idxOf_of_split_mem_B {s : List α} (hnd : s.Nodup) {A B : List α}
    {x y : α} (hAB : s = A ++ x :: B) (hyB : y ∈ B) :
    s.idxOf y = A.length + 1 + B.idxOf y := by
  obtain ⟨hdA, hdB, _, _, hdisjAB, _⟩ := split_facts hnd hAB
  have hxy : x ≠ y := fun h => hdB (h ▸ hyB)
  have hyA : y ∉ A := fun hmem => hdisjAB y hmem hyB
  have hbeq : (x == y) = false := beq_eq_false_iff_ne.mpr hxy
  rw [hAB, List.idxOf_append, if_neg hyA, List.idxOf_cons, hbeq, cond_false]
  omega

/-- `s = A ++ x :: B`、`y ∈ A` ⇒ `s.idxOf y = A.idxOf y`（且 `< A.length`）。 -/
private theorem idxOf_of_split_mem_A {s : List α} {A B : List α} {x y : α}
    (hAB : s = A ++ x :: B) (hyA : y ∈ A) :
    s.idxOf y = A.idxOf y ∧ A.idxOf y < A.length := by
  rw [hAB, List.idxOf_append, if_pos hyA]
  exact ⟨rfl, List.idxOf_lt_length_iff.mpr hyA⟩

/-- `s = A ++ x :: B` ⇒ `B = s.drop (A.length + 1)`。 -/
private theorem drop_of_split {s : List α} {A B : List α} {x : α}
    (hAB : s = A ++ x :: B) : B = s.drop (A.length + 1) := by
  rw [hAB, List.drop_append, List.drop_eq_nil_of_le (Nat.le_succ A.length),
    List.nil_append, Nat.add_sub_cancel_left, List.drop_cons (by omega : (0 : ℕ) < 1),
    List.drop_zero]

/-- `idxOf` 首现极小性：`s[p]? = some z` ⇒ `s.idxOf z ≤ p`（无 Nodup）。 -/
private theorem idxOf_le_of_getElem? {s : List α} {z : α} {p : ℕ}
    (hpz : s[p]? = some z) : s.idxOf z ≤ p := by
  induction s generalizing p with
  | nil => cases hpz
  | cons a t ih =>
    by_cases hac : a = z
    · subst hac
      rw [List.idxOf_cons_self]
      exact Nat.zero_le _
    · have hbc : (a == z) = false := beq_eq_false_iff_ne.mpr hac
      cases p with
      | zero =>
        rw [List.getElem?_cons_zero] at hpz
        exact absurd (Option.some.inj hpz) hac
      | succ q =>
        rw [List.getElem?_cons_succ] at hpz
        rw [List.idxOf_cons, hbc, cond_false]
        exact Nat.succ_le_succ (ih hpz)

/-- `take` 到自身首现位置为止：`z ∉ s.take (s.idxOf z)`。 -/
private theorem notMem_take_idxOf_self {s : List α} {z : α} (hz : z ∈ s) :
    z ∉ s.take (s.idxOf z) := by
  intro hmem
  obtain ⟨p, hp, hpw⟩ := List.getElem_of_mem hmem
  rw [List.getElem_take (h := hp)] at hpw
  have hplt : p < s.length :=
    Nat.lt_of_lt_of_le hp (by rw [List.length_take]; exact Nat.min_le_right _ _)
  have m : s[p]? = some z := by
    rw [List.getElem?_eq_getElem hplt]
    exact congrArg Option.some hpw
  have hle := idxOf_le_of_getElem? m
  have hlt2 : p < s.idxOf z :=
    Nat.lt_of_lt_of_le hp (by rw [List.length_take]; exact Nat.min_le_left _ _)
  omega

/-- `z ∉ (splitAt z s).1`（splitAtRec 首现语义，无 Nodup）。 -/
private theorem notMem_splitAt_fst_self {s : List α} {z : α} :
    z ∉ (splitAt z s).1 := by
  have main : ∀ (vs us : List α), z ∉ us → z ∉ (splitAtRec z us vs).1 := by
    intro vs us hu
    induction vs generalizing us with
    | nil => simp only [splitAtRec]; exact hu
    | cons v t ih =>
      by_cases hvz : v = z
      · subst hvz
        simp only [splitAtRec, beq_self_eq_true, reduceIte]
        exact hu
      · have hbc : (v == z) = false := beq_eq_false_iff_ne.mpr hvz
        simp only [splitAtRec, hbc]
        refine ih (us ++ [v]) (fun hmem => ?_)
        rcases List.mem_append.mp hmem with h | h
        · exact hu h
        · rcases List.mem_cons.mp h with h' | h'
          · exact hvz h'.symm
          · exact List.not_mem_nil h'
  rw [splitAt]
  exact main s [] (fun h => List.not_mem_nil h)

/-- `splitAt y s` 的前缀段即 `s.take (s.idxOf y)`。 -/
private theorem splitAt_fst_eq_take {s : List α} {y : α} (hy : y ∈ s) :
    (splitAt y s).1 = s.take (s.idxOf y) := by
  set A := (splitAt y s).1 with hA
  set B := (splitAt y s).2 with hB
  have hab : s = A ++ y :: B := by
    rw [hA, hB]
    exact splitAt_ram hy
  have hya : y ∉ A := notMem_splitAt_fst_self (s := s) (z := y)
  have hlen : s.idxOf y = A.length := by
    rw [hab, idxOf_append_of_not_mem hya, List.idxOf_cons_self]
    simp
  rw [hlen, hab, List.take_append, List.take_length, Nat.sub_self, List.take_zero,
    List.append_nil]

/-- between 展开（`x ∉ s`）：`splitAt x s = (s, [])`，取「表头到 `y`」前缀。 -/
private theorem between_eq_take_of_not_mem_left {s : List α} {x y : α}
    (hx : x ∉ s) (hy : y ∈ s) :
    between s x y = s.take (s.idxOf y) := by
  rw [← splitAt_fst_eq_take hy, between_def, splitAt_no_ram hx]
  simp

/-- between 展开（首支）：`splitAt x s = (A, B)`、`y ∈ B` 时取「`x`→`y` 段」的
头部。HOL betwn_take_drop 首支的展开形。 -/
private theorem between_eq_fst_split_of_mem {s : List α} {x y : α} {A B : List α}
    (hsp : (A, B) = splitAt x s) (hyB : y ∈ B) :
    between s x y = (splitAt y B).1 := by
  have hcb : B.contains y = true := List.contains_iff_mem.mpr hyB
  rw [between_def, ← hsp]
  show (if B.contains y then (splitAt y B).1 else B ++ (splitAt y A).1) =
    (splitAt y B).1
  rw [hcb]
  rfl

/-- between 展开（次支）：`splitAt x s = (A, B)`、`y ∉ B` 时取「绕圈段」。 -/
private theorem between_eq_append_split_of_not_mem {s : List α} {x y : α}
    {A B : List α} (hsp : (A, B) = splitAt x s) (hyB : y ∉ B) :
    between s x y = B ++ (splitAt y A).1 := by
  have hcb : B.contains y = false := by
    simpa [List.contains_iff_mem] using hyB
  rw [between_def, ← hsp]
  show (if B.contains y then (splitAt y B).1 else B ++ (splitAt y A).1) =
    B ++ (splitAt y A).1
  rw [hcb]
  rfl

end PositionAux

/-! ## §A between 位置公式（idxOf 区间刻画；HOL betwn_take_drop 机制的
idxOf 形，reduction4 链内通用层） -/

section BetweenIndex

variable {α : Type*} [DecidableEq α]

/-- **位置公式（`idxOf x < idxOf y` 分支）**：`between s x y` 是 `s` 中 `x` 之后、
`y` 之前的截段。HOL 对应 `betwn_take_drop`（tame_list.hl:1181 起）首支。 -/
theorem between_eq_take_of_idxOf_lt {s : List α} (hnd : s.Nodup) {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (hij : s.idxOf x < s.idxOf y) :
    between s x y = (s.drop (s.idxOf x + 1)).take (s.idxOf y - s.idxOf x - 1) := by
  obtain ⟨A, B, hAB⟩ := List.append_of_mem hx
  obtain ⟨hdA, hdB, _, hndB, hdisjAB, _⟩ := split_facts hnd hAB
  have hsp : (A, B) = splitAt x s := splitAt_dist_ram hnd hAB
  have hix : s.idxOf x = A.length := idxOf_self_of_split hnd hAB
  -- y ∈ B：y ∈ A 则 idxOf y < idxOf x（矛盾）；y = x 则 hij 自反矛盾
  have hyB : y ∈ B := by
    rcases List.mem_append.mp (hAB ▸ hy) with h | h
    · exfalso
      obtain ⟨h1, h2⟩ := idxOf_of_split_mem_A hAB h
      rw [hix] at hij
      omega
    · rcases List.mem_cons.mp h with h' | h'
      · rw [h'] at hij
        omega
      · exact h'
  have hBdrop := drop_of_split hAB
  -- splitAt y B 的分解
  obtain ⟨C, D, hCD⟩ := List.append_of_mem hyB
  obtain ⟨hyC, _, _, hndD, _, _⟩ := split_facts hndB hCD
  have hCfst : (splitAt y B).1 = C :=
    congrArg Prod.fst (splitAt_dist_ram hndB hCD).symm
  have hBiy : B.idxOf y = C.length := by
    rw [hCD, List.idxOf_append, if_neg hyC, List.idxOf_cons_self]
    simp
  have hBy : s.idxOf y = A.length + 1 + B.idxOf y := idxOf_of_split_mem_B hnd hAB hyB
  -- 收口：展开 between 走 true 支，两边都等于 C
  rw [between_eq_fst_split_of_mem hsp hyB]
  have hlen : A.length + 1 + C.length - A.length - 1 = C.length := by omega
  rw [hCfst, hix, hBy, hBiy, hlen, ← hBdrop, hCD, List.take_append]
  simp

/-- **位置公式（`idxOf y < idxOf x` 分支）**：`between s x y` 是「`x` 之后到表尾」
接「表头到 `y`」。HOL 对应 `betwn_take_drop` 次支。 -/
theorem between_eq_append_of_idxOf_gt {s : List α} (hnd : s.Nodup) {x y : α}
    (hx : x ∈ s) (hy : y ∈ s) (hji : s.idxOf y < s.idxOf x) :
    between s x y = s.drop (s.idxOf x + 1) ++ s.take (s.idxOf y) := by
  obtain ⟨A, B, hAB⟩ := List.append_of_mem hx
  obtain ⟨hdA, hdB, hndA, _, _, hdisjBA⟩ := split_facts hnd hAB
  have hsp : (A, B) = splitAt x s := splitAt_dist_ram hnd hAB
  have hix : s.idxOf x = A.length := idxOf_self_of_split hnd hAB
  -- y ∈ A：y ∈ B 则 idxOf y > idxOf x（矛盾）；y = x 则 hji 自反矛盾
  have hyA : y ∈ A := by
    rcases List.mem_append.mp (hAB ▸ hy) with h | h
    · exact h
    · exfalso
      rcases List.mem_cons.mp h with h' | h'
      · rw [h'] at hji
        omega
      · rw [hix] at hji
        have hBy : s.idxOf y = A.length + 1 + B.idxOf y :=
          idxOf_of_split_mem_B hnd hAB h'
        omega
  have hyB : y ∉ B := fun hmem => hdisjBA y hmem hyA
  -- splitAt y A 的分解
  obtain ⟨C, D, hCD⟩ := List.append_of_mem hyA
  obtain ⟨hyC, _, _, _, _, _⟩ := split_facts hndA hCD
  have hAfst : (splitAt y A).1 = C :=
    congrArg Prod.fst (splitAt_dist_ram hndA hCD).symm
  have hiy : s.idxOf y = C.length := by
    rw [hAB, List.idxOf_append, if_pos hyA, hCD, List.idxOf_append, if_neg hyC,
      List.idxOf_cons_self]
    simp
  -- 收口：展开 between 走 false 支
  rw [between_eq_append_split_of_not_mem hsp hyB]
  have hAB2 : s = C ++ (y :: D ++ x :: B) := by
    subst hCD
    rw [hAB, List.append_assoc]
  have hstake : s.take C.length = C := by
    rw [hAB2, List.take_append]
    simp
  have hBdrop := drop_of_split hAB
  rw [hAfst, hix, hiy, ← hBdrop, hstake]

end BetweenIndex

/-! ## §B 成员往返（位置区间 ⇔ between 成员） -/

section BetweenMembers

variable {α : Type*} [DecidableEq α]

/-- 位置→成员（`idxOf x < idxOf y` 支）：严格夹在 `x`、`y` 位置之间的元素
落在 `between s x y` 里。 -/
theorem mem_between_of_idxOf_lt {s : List α} (hnd : s.Nodup) {x y w : α}
    (hx : x ∈ s) (hy : y ∈ s) (hij : s.idxOf x < s.idxOf y)
    (hik : s.idxOf x < s.idxOf w) (hkw : s.idxOf w < s.idxOf y) (hw : w ∈ s) :
    w ∈ between s x y := by
  rw [between_eq_take_of_idxOf_lt hnd hx hy hij]
  have hk : s.idxOf w < s.length := List.idxOf_lt_length_iff.mpr hw
  have hval : s[s.idxOf w]'(List.idxOf_lt_length_iff.mpr hw) = w := getElem_idxOf_mem hw
  have hp : s.idxOf w - (s.idxOf x + 1) <
      ((s.drop (s.idxOf x + 1)).take (s.idxOf y - s.idxOf x - 1)).length := by
    rw [List.length_take, List.length_drop]
    omega
  have hp2 : s.idxOf w - (s.idxOf x + 1) < s.idxOf y - s.idxOf x - 1 :=
    Nat.lt_of_lt_of_le hp (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have hp3 : s.idxOf w - (s.idxOf x + 1) < (s.drop (s.idxOf x + 1)).length := by
    rw [List.length_drop]
    omega
  have hele : ((s.drop (s.idxOf x + 1)).take (s.idxOf y - s.idxOf x - 1))[s.idxOf w -
      (s.idxOf x + 1)]? = some w := by
    rw [List.getElem?_eq_getElem (h := hp), List.getElem_take (h := hp),
      List.getElem_drop (h := hp3)]
    have hide : s.idxOf x + 1 + (s.idxOf w - (s.idxOf x + 1)) = s.idxOf w := by omega
    simp only [hide, hval]
  obtain ⟨hpv, hpve⟩ := List.getElem?_eq_some_iff.mp hele
  rw [← hpve]
  exact List.getElem_mem hpv

/-- 位置→成员（`idxOf y < idxOf x` 支）。 -/
theorem mem_between_of_idxOf_gt {s : List α} (hnd : s.Nodup) {x y w : α}
    (hx : x ∈ s) (hy : y ∈ s) (hji : s.idxOf y < s.idxOf x)
    (h : s.idxOf x < s.idxOf w ∨ s.idxOf w < s.idxOf y) (hw : w ∈ s) :
    w ∈ between s x y := by
  rw [between_eq_append_of_idxOf_gt hnd hx hy hji]
  have hk : s.idxOf w < s.length := List.idxOf_lt_length_iff.mpr hw
  have hval : s[s.idxOf w]'(List.idxOf_lt_length_iff.mpr hw) = w := getElem_idxOf_mem hw
  rcases h with hkx | hky
  · refine List.mem_append.mpr (Or.inl ?_)
    have hp : s.idxOf w - (s.idxOf x + 1) < (s.drop (s.idxOf x + 1)).length := by
      rw [List.length_drop]
      omega
    have hele : (s.drop (s.idxOf x + 1))[s.idxOf w - (s.idxOf x + 1)]? = some w := by
      rw [List.getElem?_eq_getElem (h := hp), List.getElem_drop (h := hp)]
      have hide : s.idxOf x + 1 + (s.idxOf w - (s.idxOf x + 1)) = s.idxOf w := by omega
      simp only [hide, hval]
    have ⟨hpv, hpve⟩ := List.getElem?_eq_some_iff.mp hele
    rw [← hpve]
    exact List.getElem_mem hpv
  · refine List.mem_append.mpr (Or.inr ?_)
    have hp : s.idxOf w < (s.take (s.idxOf y)).length := by
      rw [List.length_take]
      exact lt_min hky hk
    have hele : (s.take (s.idxOf y))[s.idxOf w]? = some w := by
      rw [List.getElem?_eq_getElem (h := hp), List.getElem_take (h := hp)]
      exact congrArg Option.some hval
    have ⟨hpv, hpve⟩ := List.getElem?_eq_some_iff.mp hele
    rw [← hpve]
    exact List.getElem_mem hpv

/-- 成员→位置（`idxOf x < idxOf y` 支）：`between` 成员的位置严格夹在中间。 -/
theorem idxOf_mem_between_of_lt {s : List α} (hnd : s.Nodup) {x y w : α}
    (hx : x ∈ s) (hy : y ∈ s) (hij : s.idxOf x < s.idxOf y)
    (hw : w ∈ between s x y) :
    s.idxOf x < s.idxOf w ∧ s.idxOf w < s.idxOf y := by
  rw [between_eq_take_of_idxOf_lt hnd hx hy hij] at hw
  obtain ⟨p, hp, hpw⟩ := List.getElem_of_mem hw
  have hptake : p < (s.drop (s.idxOf x + 1)).length :=
    Nat.lt_of_lt_of_le hp (by rw [List.length_take]; exact Nat.min_le_right _ _)
  have hptake2 : p < s.idxOf y - s.idxOf x - 1 :=
    Nat.lt_of_lt_of_le hp (by rw [List.length_take]; exact Nat.min_le_left _ _)
  rw [List.getElem_take (h := hp), List.getElem_drop (h := hptake)] at hpw
  have hlt : s.idxOf x + 1 + p < s.length := by
    have := hptake
    rw [List.length_drop] at this
    omega
  have hk : s.idxOf w = s.idxOf x + 1 + p := idxOf_eq_of_getElem hnd hlt hpw
  omega

/-- 成员→位置（`idxOf y < idxOf x` 支）。 -/
theorem idxOf_mem_between_of_gt {s : List α} (hnd : s.Nodup) {x y w : α}
    (hx : x ∈ s) (hy : y ∈ s) (hji : s.idxOf y < s.idxOf x)
    (hw : w ∈ between s x y) :
    s.idxOf x < s.idxOf w ∨ s.idxOf w < s.idxOf y := by
  rw [between_eq_append_of_idxOf_gt hnd hx hy hji] at hw
  rcases List.mem_append.mp hw with h | h
  · refine Or.inl ?_
    obtain ⟨p, hp, hpw⟩ := List.getElem_of_mem h
    rw [List.getElem_drop (h := hp)] at hpw
    have hlt : s.idxOf x + 1 + p < s.length := by
      have := hp
      rw [List.length_drop] at this
      omega
    have hk : s.idxOf w = s.idxOf x + 1 + p := idxOf_eq_of_getElem hnd hlt hpw
    omega
  · refine Or.inr ?_
    obtain ⟨p, hp, hpw⟩ := List.getElem_of_mem h
    rw [List.getElem_take (h := hp)] at hpw
    have hplen : p < s.length :=
      Nat.lt_of_lt_of_le hp (by rw [List.length_take]; exact Nat.min_le_right _ _)
    have hk : s.idxOf w = p := idxOf_eq_of_getElem hnd hplen hpw
    have hk2 : p < s.idxOf y :=
      Nat.lt_of_lt_of_le hp (by rw [List.length_take]; exact Nat.min_le_left _ _)
    omega

end BetweenMembers

/-! ## §C betwn 三件（not_betwn1/2 + betwn_cases 外科内联 + betwn_disjoint） -/

section BetweenProps

variable {α : Type*} [DecidableEq α]

/-- **HOL `not_betwn1`**（tame_list.hl:2574）：`Nodup s`、`z ∈ s` ⇒
`x ∉ between s x z`。 -/
theorem notBetwn1 {s : List α} (hnd : s.Nodup) {x z : α} (hz : z ∈ s) :
    x ∉ between s x z := by
  intro hmem
  by_cases hx : x ∈ s
  · by_cases hxz : x = z
    · subst hxz
      exact ((set_between_id hnd hx).mp hmem).2 rfl
    · by_cases hij : s.idxOf x < s.idxOf z
      · have := (idxOf_mem_between_of_lt hnd hx hz hij hmem).1
        omega
      · have hji : s.idxOf z < s.idxOf x := by
          have hne : s.idxOf x ≠ s.idxOf z := fun h => hxz (eq_of_idxOf_eq hnd hx hz h)
          omega
        have := idxOf_mem_between_of_gt hnd hx hz hji hmem
        omega
  · exact hx (inbetween_inset hmem)

/-- **HOL `not_betwn2`**（tame_list.hl:2600）：`Nodup s` ⇒
`z ∉ between s x z`。 -/
theorem notBetwn2 {s : List α} (hnd : s.Nodup) {x z : α} :
    z ∉ between s x z := by
  intro hmem
  by_cases hz : z ∈ s
  · by_cases hxz : x = z
    · subst hxz
      exact ((set_between_id hnd hz).mp hmem).2 rfl
    · by_cases hx : x ∈ s
      · by_cases hij : s.idxOf x < s.idxOf z
        · have := (idxOf_mem_between_of_lt hnd hx hz hij hmem).2
          omega
        · have hji : s.idxOf z < s.idxOf x := by
            have hne : s.idxOf x ≠ s.idxOf z := fun h => hxz (eq_of_idxOf_eq hnd hx hz h)
            omega
          have := idxOf_mem_between_of_gt hnd hx hz hji hmem
          omega
      · rw [between_eq_take_of_not_mem_left hx hz] at hmem
        exact notMem_take_idxOf_self hz hmem
  · exact hz (inbetween_inset hmem)

/-- **HOL `betwn_cases`**（tame_list.hl:2744）：三不同元素的四路划分。 -/
theorem betwnMemCover {s : List α} (hnd : s.Nodup) {x y z : α}
    (hxz : x ≠ z) (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) :
    y = x ∨ y = z ∨ y ∈ between s x z ∨ y ∈ between s z x := by
  by_cases hyx : y = x
  · exact Or.inl hyx
  by_cases hyz : y = z
  · exact Or.inr (Or.inl hyz)
  have hxy : x ≠ y := fun h => hyx h.symm
  have hixz : s.idxOf x ≠ s.idxOf z := fun h => hxz (eq_of_idxOf_eq hnd hx hz h)
  have hixy : s.idxOf x ≠ s.idxOf y := fun h => hxy (eq_of_idxOf_eq hnd hx hy h)
  have hiyz : s.idxOf y ≠ s.idxOf z := fun h => hyz (eq_of_idxOf_eq hnd hy hz h)
  by_cases hij : s.idxOf x < s.idxOf z
  · -- 位置序 i < j（x 在 z 前）
    by_cases hky : s.idxOf y < s.idxOf z
    · -- c := idxOf y < j：子分裂 c vs i
      by_cases hiky : s.idxOf x < s.idxOf y
      · -- i < c < j：y ∈ between s x z（首支 lt）
        exact Or.inr (Or.inr (Or.inl
          (mem_between_of_idxOf_lt hnd hx hz hij hiky hky hy)))
      · -- c < i（且 c < j）：y ∈ between s z x（次支 gt，右片 c < j）
        have hkx : s.idxOf y < s.idxOf x := by omega
        exact Or.inr (Or.inr (Or.inr
          (mem_between_of_idxOf_gt hnd hz hx hij (Or.inr hkx) hy)))
    · -- j < c（y 在 z 之后）：y ∈ between s z x（次支 gt，左片 j < c）
      exact Or.inr (Or.inr (Or.inr
        (mem_between_of_idxOf_gt hnd hz hx hij (Or.inl (by omega)) hy)))
  · -- 位置序 j < i（z 在 x 前）
    have hji : s.idxOf z < s.idxOf x := by omega
    by_cases hky : s.idxOf y < s.idxOf z
    · -- c < j：子分裂 c vs i
      by_cases hkx : s.idxOf y < s.idxOf x
      · -- c < j ∧ c < i：y ∈ between s x z（次支 gt，右片 c < j）→ third
        exact Or.inr (Or.inr (Or.inl
          (mem_between_of_idxOf_gt hnd hx hz hji (Or.inr hky) hy)))
      · -- c < j ∧ i < c（j < i < c）：y ∈ between s z x（首支 lt，j < c < i）→ fourth
        exact Or.inr (Or.inr (Or.inr
          (mem_between_of_idxOf_lt hnd hz hx hji (by omega) (by omega) hy)))
    · -- j < c：子分裂 c vs i
      by_cases hkx : s.idxOf y < s.idxOf x
      · -- j < c ∧ c < i：y ∈ between s z x（首支 lt，j < c < i）
        exact Or.inr (Or.inr (Or.inr
          (mem_between_of_idxOf_lt hnd hz hx hji (by omega) hkx hy)))
      · -- j < c ∧ i < c：y ∈ between s x z（次支 gt，左片 i < c）
        exact Or.inr (Or.inr (Or.inl
          (mem_between_of_idxOf_gt hnd hx hz hji (Or.inl (by omega)) hy)))

/-- **HOL `betwn_disjoint`**（reduction3.hl:2851，J3 领土外科内联）：不同元素
的两个 between 弧不相交。 -/
theorem betwnDisjoint {s : List α} (hnd : s.Nodup) {x y w : α}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (hw : w ∈ between s x y) :
    w ∉ between s y x := by
  intro hmem
  by_cases hij : s.idxOf x < s.idxOf y
  · have h1 := idxOf_mem_between_of_lt hnd hx hy hij hw
    have h2 := idxOf_mem_between_of_gt hnd hy hx (by omega) hmem
    omega
  · have hji : s.idxOf y < s.idxOf x := by
      have hne : s.idxOf x ≠ s.idxOf y := fun h => hxy (eq_of_idxOf_eq hnd hx hy h)
      omega
    have h1 := idxOf_mem_between_of_lt hnd hy hx hji hmem
    have h2 := idxOf_mem_between_of_gt hnd hx hy hji hw
    omega

end BetweenProps

/-! ## §D ifbetwn 四件（reduction4.hl 本地层；
载体 `Kepler.Text.Reduction5.ifbetwn`，Reduction5Base:216） -/

section IfbetwnProps

variable {α : Type*} [DecidableEq α]

/-- **HOL `ifbetwn_refl`**（reduction4.hl:4499）。 -/
theorem ifbetwnRefl (s : List α) (x : α) : ifbetwn s x x = [] := by
  simp [ifbetwn]

/-- **HOL `mem_ifbetwn`**（reduction4.hl:2746）：`ifbetwn` 成员都是 `s` 成员。 -/
theorem memOfMemIfbetwn {s : List α} {x y u : α} (h : u ∈ ifbetwn s x y) :
    u ∈ s := by
  unfold ifbetwn at h
  by_cases hc : x ∈ s ∧ y ∈ s ∧ x ≠ y
  · rw [if_pos hc] at h
    rcases List.mem_append.mp h with h' | h'
    · exact inbetween_inset h'
    · rcases List.mem_cons.mp h' with rfl | h'
      · exact hc.2.1
      · exact absurd h' (List.not_mem_nil)
  · rw [if_neg hc] at h
    exact absurd h List.not_mem_nil

/-- **HOL `ifbetwn_disjoint`**（reduction4.hl:3803）：`ifbetwn f x y` 与
`ifbetwn f y x` 不相交。 -/
theorem ifbetwnDisjoint {s : List α} (hnd : s.Nodup) {x y w : α}
    (hw : w ∈ ifbetwn s x y) : w ∉ ifbetwn s y x := by
  unfold ifbetwn at hw
  by_cases hc : x ∈ s ∧ y ∈ s ∧ x ≠ y
  · have hx : x ∈ s := hc.1
    have hy : y ∈ s := hc.2.1
    have hxy : x ≠ y := hc.2.2
    rw [if_pos hc] at hw
    intro hm
    unfold ifbetwn at hm
    rw [if_pos (show y ∈ s ∧ x ∈ s ∧ y ≠ x from ⟨hy, hx, fun h => hxy h.symm⟩)] at hm
    rcases List.mem_append.mp hw with hw' | hw2
    · rcases List.mem_append.mp hm with hm' | hm2
      · exact betwnDisjoint hnd hx hy hxy hw' hm'
      · rcases List.mem_cons.mp hm2 with hme | hme
        · subst hme
          exact notBetwn1 hnd hy hw'
        · exact List.not_mem_nil hme
    · rcases List.mem_cons.mp hw2 with hwe | hwe
      · subst hwe
        rcases List.mem_append.mp hm with hm' | hm2
        · exact notBetwn1 hnd hx hm'
        · rcases List.mem_cons.mp hm2 with hme | hme
          · exact hxy hme.symm
          · exact List.not_mem_nil hme
      · exact List.not_mem_nil hwe
  · rw [if_neg hc] at hw
    exact absurd hw List.not_mem_nil

/-- **HOL `ifbetwn_cover`**（reduction4.hl:3818）：三成员、两不同端点的
互补划分。 -/
theorem ifbetwnCover {s : List α} (hnd : s.Nodup) {x y w : α}
    (hx : x ∈ s) (hy : y ∈ s) (hw : w ∈ s) (hxy : x ≠ y) :
    w ∈ ifbetwn s x y ↔ w ∉ ifbetwn s y x := by
  constructor
  · intro h
    exact ifbetwnDisjoint hnd h
  · intro h
    have hcondR : y ∈ s ∧ x ∈ s ∧ y ≠ x := ⟨hy, hx, fun h => hxy h.symm⟩
    unfold ifbetwn at h
    rw [if_pos hcondR] at h
    unfold ifbetwn
    rw [if_pos (⟨hx, hy, hxy⟩ : x ∈ s ∧ y ∈ s ∧ x ≠ y)]
    by_cases hwy : w = y
    · exact List.mem_append.mpr (Or.inr (by rw [hwy]; exact List.mem_cons_self))
    · have hwx : w ≠ x := by
        intro hwx2
        exact h (List.mem_append.mpr (Or.inr (by rw [← hwx2]; exact List.mem_cons_self)))
      rcases betwnMemCover hnd hxy hx hw hy with h1 | h2 | h3 | h4
      · exact absurd h1 hwx
      · exact absurd h2 hwy
      · exact List.mem_append.mpr (Or.inl h3)
      · exact absurd (List.mem_append.mpr (Or.inl h4)) h

end IfbetwnProps

end Kepler.Text.Reduction4

/-! 公理审计锚（本文件编译即执行；预期 = 标准三
`[propext, Classical.choice, Quot.sound]`，零 sorryAx。落库时编排者可整体
注释本节，不影响任何声明。） -/
#print axioms Kepler.Text.Reduction4.between_eq_take_of_idxOf_lt
#print axioms Kepler.Text.Reduction4.between_eq_append_of_idxOf_gt
#print axioms Kepler.Text.Reduction4.mem_between_of_idxOf_lt
#print axioms Kepler.Text.Reduction4.mem_between_of_idxOf_gt
#print axioms Kepler.Text.Reduction4.idxOf_mem_between_of_lt
#print axioms Kepler.Text.Reduction4.idxOf_mem_between_of_gt
#print axioms Kepler.Text.Reduction4.notBetwn1
#print axioms Kepler.Text.Reduction4.notBetwn2
#print axioms Kepler.Text.Reduction4.betwnMemCover
#print axioms Kepler.Text.Reduction4.betwnDisjoint
#print axioms Kepler.Text.Reduction4.ifbetwnRefl
#print axioms Kepler.Text.Reduction4.memOfMemIfbetwn
#print axioms Kepler.Text.Reduction4.ifbetwnDisjoint
#print axioms Kepler.Text.Reduction4.ifbetwnCover
