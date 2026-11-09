/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12I — AQ12 叶 W4b-ii（decl 28）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:1215-:1339（125 HOL 行）
  `uniq(flatten r) ∧ MEM d (flatten (betwn r v v1)) ∧ MEM y v ∧ MEM z v1 ∧
     ~(v=v1) ∧ MEM v r ∧ MEM v1 r ∧ all nonempty r ==>
     MEM d (betwn (flatten r) y z)`

  ┌─ 路线（HOL 的逐支 indexf 不等式 vs Lean 的「块定位 + idxOf 序」）────
  │ ① 两个 `betwnTakeDrop` 情形把 `r.flatten` 切成三段（与 W4b-i 同款）：
  │    iv<iv1：`P ++ a.flatten ++ T`（a 在中间）；
  │    iv1<iv：`A' ++ M ++ D` 且 `a.flatten = D ++ A'`（环绕）。
  │ ② 块内定位：y ∈ v ⟹ y ∈ 某块、z ∈ v1 ⟹ z ∈ 某块、d ∈ a.flatten ⟹ d ∈ D 或 A'；
  │    环绕支再把 `M`（parts 层）拆成 `v1 :: (W ++ [v])` 得到 z 在 y 之前。
  │ ③ 全部化归 `idxOf` 的序（三段块链 + 同块保序），最后由两条
  │    `indexfBetwnEq` 收口件（`aqs_mem_betwn_of_idx_lt` / `_wrap`）给出
  │    `d ∈ betwn (flatten r) y z`。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与去重纪律 ─────────────────────────────────────────────
  │ · parts 层的 `betwn`/`nextEl` 一律用泛型原件（`HD_BETWN2` 等，
  │   `LawfulBEq (List (ℕ × ℕ))` 实例实测存在）；不造 dart 固定副本。
  │ · `mem_flatten_betwn_sym` 是 **J2 more_lemma1 消费件 ⇒ 公开**（`aqs_` 前缀）。
  └────────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12H

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between)

/-! ## §0 块序辅件 -/

/-- 左块元素在拼接表中的 idxOf 小于右块元素。 -/
private theorem aqs_idxOf_lt_of_mem_left {P R : List (ℕ × ℕ)} (hnd : (P ++ R).Nodup)
    {a b : ℕ × ℕ} (ha : a ∈ P) (hb : b ∈ R) : (P ++ R).idxOf a < (P ++ R).idxOf b := by
  obtain ⟨hP, hR, hdisj⟩ := List.nodup_append.mp hnd
  have hbP : b ∉ P := fun h => hdisj _ h _ hb rfl
  have h1 : (P ++ R).idxOf a = P.idxOf a := by
    rw [List.idxOf_append, if_pos ha]
  have h2 : (P ++ R).idxOf b = R.idxOf b + P.length := by
    rw [List.idxOf_append, if_neg hbP]
  rw [h1, h2]
  have := List.idxOf_lt_length_iff.mpr ha
  omega

/-- 同块元素在拼接表中保持 idxOf 序。 -/
private theorem aqs_idxOf_lt_same_block {P X T : List (ℕ × ℕ)}
    (hnd : (P ++ X ++ T).Nodup) {a b : ℕ × ℕ} (ha : a ∈ X) (hb : b ∈ X)
    (h : X.idxOf a < X.idxOf b) : (P ++ X ++ T).idxOf a < (P ++ X ++ T).idxOf b := by
  have hnd' : (P ++ (X ++ T)).Nodup := by rwa [List.append_assoc] at hnd
  obtain ⟨hP, hXT, hdisjP⟩ := List.nodup_append.mp hnd'
  obtain ⟨-, -, hdisjX⟩ := List.nodup_append.mp hXT
  have haP : a ∉ P := fun h' => hdisjP _ h' _ (List.mem_append.mpr (Or.inl ha)) rfl
  have hbP : b ∉ P := fun h' => hdisjP _ h' _ (List.mem_append.mpr (Or.inl hb)) rfl
  have haT : a ∉ T := fun h' => hdisjX _ ha _ h' rfl
  have hbT : b ∉ T := fun h' => hdisjX _ hb _ h' rfl
  have h1 : (P ++ X ++ T).idxOf a = X.idxOf a + P.length := by
    rw [List.append_assoc, List.idxOf_append_of_notMem haP, List.idxOf_append, if_pos ha]
    omega
  have h2 : (P ++ X ++ T).idxOf b = X.idxOf b + P.length := by
    rw [List.append_assoc, List.idxOf_append_of_notMem hbP, List.idxOf_append, if_pos hb]
    omega
  omega

/-- 线性在前的三块定位 ⇒ `idxOf` 双严格序。 -/
private theorem aqs_idx_lt_of_blocks {P X T : List (ℕ × ℕ)}
    (hnd : (P ++ X ++ T).Nodup) {a b c : ℕ × ℕ} (ha : a ∈ P) (hb : b ∈ X)
    (hc : c ∈ T) :
    (P ++ X ++ T).idxOf a < (P ++ X ++ T).idxOf b ∧
      (P ++ X ++ T).idxOf b < (P ++ X ++ T).idxOf c := by
  have hnd' : (P ++ (X ++ T)).Nodup := by rwa [List.append_assoc] at hnd
  constructor
  · have h' := aqs_idxOf_lt_of_mem_left hnd' ha (List.mem_append.mpr (Or.inl hb))
    simpa only [List.append_assoc] using h'
  · exact aqs_idxOf_lt_of_mem_left hnd (List.mem_append.mpr (Or.inr hb)) hc

/-- `idxOf` 双严格序（线性支）⇒ between 成员。 -/
private theorem aqs_mem_betwn_of_idx_lt {S : List (ℕ × ℕ)} (hnd : S.Nodup)
    {y d z : ℕ × ℕ} (hy : y ∈ S) (hd : d ∈ S) (hz : z ∈ S)
    (h1 : S.idxOf y < S.idxOf d) (h2 : S.idxOf d < S.idxOf z) :
    d ∈ between S y z := by
  have hyz : y ≠ z := fun h => by subst h; omega
  have hyzlt : S.idxOf y < S.idxOf z := lt_trans h1 h2
  refine (indexfBetwnEq hyz hnd hy hz).mpr ⟨?_, ?_⟩
  · rw [indexfCond hy hd, if_pos (le_of_lt h1)]
    omega
  · rw [indexfCond hy hd, indexfCond hy hz, if_pos (le_of_lt h1),
      if_pos (le_of_lt hyzlt)]
    omega

/-- `idxOf` 环绕序 ⇒ between 成员（y 在 z 之后，d 在 y 之后或 z 之前）。 -/
private theorem aqs_mem_betwn_of_idx_wrap {S : List (ℕ × ℕ)} (hnd : S.Nodup)
    {y d z : ℕ × ℕ} (hy : y ∈ S) (hd : d ∈ S) (hz : z ∈ S)
    (hzy : S.idxOf z < S.idxOf y)
    (hcase : S.idxOf y < S.idxOf d ∨ S.idxOf d < S.idxOf z) :
    d ∈ between S y z := by
  have hyz : y ≠ z := fun h => by subst h; omega
  have hyd : y ≠ d := fun h => by subst h; omega
  have hN : S.length ≤ S.length := le_rfl
  have hyN : S.idxOf y < S.length := List.idxOf_lt_length_iff.mpr hy
  have hdN : S.idxOf d < S.length := List.idxOf_lt_length_iff.mpr hd
  have hzN : S.idxOf z < S.length := List.idxOf_lt_length_iff.mpr hz
  -- indexf y d > 0
  have hpos : 0 < indexf y d S := by
    rw [indexfCond hy hd]
    rcases hcase with h | h
    · rw [if_pos (le_of_lt h)]; omega
    · rw [if_neg (by omega)]
      omega
  -- indexf y z = 环绕形
  have hzform : indexf y z S = S.idxOf z + (S.length - S.idxOf y) := by
    rw [indexfCond hy hz, if_neg (by omega)]
  have hlt : indexf y d S < indexf y z S := by
    rw [hzform]
    rw [indexfCond hy hd]
    rcases hcase with h | h
    · rw [if_pos (le_of_lt h)]; omega
    · rw [if_neg (by omega)]; omega
  exact (indexfBetwnEq hyz hnd hy hz).mpr ⟨hpos, hlt⟩

/-- `idxOf` 在 Nodup 表上单射（parts 层，泛型）。 -/
private theorem aqs_idxOf_inj {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] {r : List α}
    (hr : r.Nodup) {a b : α} (ha : a ∈ r) (hb : b ∈ r) (h : r.idxOf a = r.idxOf b) : a = b := by
  have hlt_a : r.idxOf a < r.length := List.idxOf_lt_length_iff.mpr ha
  have hlt_b : r.idxOf b < r.length := List.idxOf_lt_length_iff.mpr hb
  have e1 : r[r.idxOf a]? = some a := by
    rw [List.getElem?_eq_getElem hlt_a, List.getElem_idxOf hlt_a]
  have e2 : r[r.idxOf b]? = some b := by
    rw [List.getElem?_eq_getElem hlt_b, List.getElem_idxOf hlt_b]
  have h' : r[r.idxOf a]? = r[r.idxOf b]? := by rw [h]
  rw [e1, e2] at h'
  exact Option.some.inj h'

/-- 成员在 `drop k` 中 ⇒ `k ≤ idxOf`（Nodup）。 -/
private theorem aqs_idxOf_ge_of_mem_drop {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {r : List α} (hr : r.Nodup) {x : α} {k : ℕ} (h : x ∈ r.drop k) : k ≤ r.idxOf x := by
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp h
  have hjn : k + j < r.length := by rw [List.length_drop] at hj; omega
  have hxr : r[k + j] = x := by rw [← hget]; exact (List.getElem_drop).symm
  rw [← hxr, Kepler.Text.TameLp.idxOf_getElem hr hjn]
  omega

/-- 成员在 `take n` 中 ⇒ `idxOf < n`（Nodup）。 -/
private theorem aqs_idxOf_lt_of_mem_take {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {r : List α} (hr : r.Nodup) {x : α} {n : ℕ} (h : x ∈ r.take n) : r.idxOf x < n := by
  obtain ⟨j, hj, hget⟩ := List.mem_take_iff_getElem.mp h
  have hjn : j < r.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
  have hn : j < n := lt_of_lt_of_le hj (Nat.min_le_left _ _)
  rw [← hget, Kepler.Text.TameLp.idxOf_getElem hr hjn]
  exact hn

/-- 成员在 `drop k` 中 ⇒ 全表 idxOf = k + 子表 idxOf。 -/
private theorem aqs_idxOf_mem_drop_eq {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {r : List α} (hr : r.Nodup) {x : α} {k : ℕ} (h : x ∈ r.drop k) :
    r.idxOf x = k + (r.drop k).idxOf x := by
  have hj : (r.drop k).idxOf x < (r.drop k).length := List.idxOf_lt_length_iff.mpr h
  have hx1 : (r.drop k)[(r.drop k).idxOf x] = x := List.getElem_idxOf hj
  have hk : k + (r.drop k).idxOf x < r.length := by rw [List.length_drop] at hj; omega
  have hx2 : r[k + (r.drop k).idxOf x]'hk = x := by
    have h2 : (r.drop k)[(r.drop k).idxOf x]'hj = r[k + (r.drop k).idxOf x]'hk :=
      List.getElem_drop
    rw [← h2]
    exact List.getElem_idxOf hj
  calc r.idxOf x = r.idxOf (r[k + (r.drop k).idxOf x]'hk) := by rw [hx2]
    _ = k + (r.drop k).idxOf x := Kepler.Text.TameLp.idxOf_getElem hr hk

/-- 成员在 parts 层的位置序 ⇒ flatten 层的 idxOf 严格序：
`p` 在 `q` 之前（parts 层），则 `p` 内元素在 flatten 中先于 `q` 内元素。 -/
private theorem aqs_flatIdx_lt_of_partIdx_lt {r : List (List (ℕ × ℕ))}
    (hflat : r.flatten.Nodup) {p q : List (ℕ × ℕ)} (hp : p ∈ r) (hq : q ∈ r)
    (hpq : r.idxOf p < r.idxOf q) {a b : ℕ × ℕ} (ha : a ∈ p) (hb : b ∈ q) :
    r.flatten.idxOf a < r.flatten.idxOf b := by
  have hip : r.idxOf p < r.length := List.idxOf_lt_length_iff.mpr hp
  have hiq : r.idxOf q < r.length := List.idxOf_lt_length_iff.mpr hq
  have hdrop : r.drop (r.idxOf p) = p :: r.drop (r.idxOf p + 1) := by
    rw [List.drop_eq_getElem_cons hip, List.getElem_idxOf hip]
  have hdec : r.flatten = (r.take (r.idxOf p)).flatten ++ p
      ++ (r.drop (r.idxOf p + 1)).flatten := by
    have hr : r = r.take (r.idxOf p) ++ p :: r.drop (r.idxOf p + 1) := by
      calc r = r.take (r.idxOf p) ++ r.drop (r.idxOf p) := (List.take_append_drop _ _).symm
        _ = r.take (r.idxOf p) ++ (p :: r.drop (r.idxOf p + 1)) := by rw [hdrop]
    have := congrArg List.flatten hr
    simp only [List.flatten_append, List.flatten_cons] at this
    rw [this, List.append_assoc]
  have hmemq : q ∈ r.drop (r.idxOf p + 1) := by
    have hlt : r.idxOf q - (r.idxOf p + 1) < (r.drop (r.idxOf p + 1)).length := by
      rw [List.length_drop]
      omega
    have hget : (r.drop (r.idxOf p + 1))[r.idxOf q - (r.idxOf p + 1)]'hlt
        = r[r.idxOf q]'hiq := by
      rw [List.getElem_drop]
      congr 1
      omega
    have hmem : (r.drop (r.idxOf p + 1))[r.idxOf q - (r.idxOf p + 1)]'hlt
        ∈ r.drop (r.idxOf p + 1) := List.getElem_mem hlt
    rw [hget, List.getElem_idxOf hiq] at hmem
    exact hmem
  have hbT : b ∈ (r.drop (r.idxOf p + 1)).flatten :=
    List.mem_flatten.mpr ⟨q, hmemq, hb⟩
  have hndD : ((r.take (r.idxOf p)).flatten ++ p
      ++ (r.drop (r.idxOf p + 1)).flatten).Nodup := by
    rw [← hdec]
    exact hflat
  have h := aqs_idxOf_lt_of_mem_left hndD (List.mem_append.mpr (Or.inr ha)) hbT
  rwa [← hdec] at h

/-! ## §1 HOL AQ12.hl:1215 `mem_flatten_betwn_sym` -/

/-- **HOL `mem_flatten_betwn_sym`**（AQ12.hl:1215-:1339）：
`d` 在环段 flatten 中 ⇒ `d` 在 flatten 层 `betwn r.flatten y z` 中
（`y ∈ v`、`z ∈ v1`）。**J2 more_lemma1 消费 ⇒ 公开件**。 -/
theorem aqs_memFlattenBetwnSym {r : List (List (ℕ × ℕ))} {v v1 : List (ℕ × ℕ)}
    {d y z : ℕ × ℕ} (hflat : r.flatten.Nodup) (hd : d ∈ (between r v v1).flatten)
    (hy : y ∈ v) (hz : z ∈ v1) (hvne : v ≠ v1) (hv : v ∈ r) (hv1 : v1 ∈ r)
    (hall : ∀ l ∈ r, l ≠ []) : d ∈ between r.flatten y z := by
  have hrnd : r.Nodup := uniqFlatten hflat hall
  have hyS : y ∈ r.flatten := List.mem_flatten.mpr ⟨v, hv, hy⟩
  have hzS : z ∈ r.flatten := List.mem_flatten.mpr ⟨v1, hv1, hz⟩
  obtain ⟨p, hp, hdp⟩ := List.mem_flatten.mp hd
  have hp_r : p ∈ r := betwnMem hp
  have hdS : d ∈ r.flatten := List.mem_flatten.mpr ⟨p, hp_r, hdp⟩
  have hvne_idx : r.idxOf v ≠ r.idxOf v1 := fun h => hvne (aqs_idxOf_inj hrnd hv hv1 h)
  by_cases h1 : r.idxOf v < r.idxOf v1
  · -- take 支：iv < ip < iv1
    have hBform : between r v v1
        = (r.drop (r.idxOf v + 1)).take (r.idxOf v1 - (r.idxOf v + 1)) := by
      rw [betwnTakeDrop hrnd hv1, if_pos h1]
    have hp_mem : p ∈ (r.drop (r.idxOf v + 1)).take (r.idxOf v1 - (r.idxOf v + 1)) := by
      rw [← hBform]
      exact hp
    have hp_drop : p ∈ r.drop (r.idxOf v + 1) := List.mem_of_mem_take hp_mem
    have hk : r.idxOf v < r.idxOf p := by
      have hk1 : r.idxOf v + 1 ≤ r.idxOf p := aqs_idxOf_ge_of_mem_drop hrnd hp_drop
      omega
    have hp_lt : r.idxOf p < r.idxOf v1 := by
      have hsubidx : (r.drop (r.idxOf v + 1)).idxOf p
          < r.idxOf v1 - (r.idxOf v + 1) :=
        aqs_idxOf_lt_of_mem_take ((List.drop_sublist _ _).nodup hrnd) hp_mem
      have heq : r.idxOf p
          = (r.idxOf v + 1) + (r.drop (r.idxOf v + 1)).idxOf p :=
        aqs_idxOf_mem_drop_eq hrnd hp_drop
      omega
    exact aqs_mem_betwn_of_idx_lt hflat hyS hdS hzS
      (aqs_flatIdx_lt_of_partIdx_lt hflat hv hp_r hk hy hdp)
      (aqs_flatIdx_lt_of_partIdx_lt hflat hp_r hv1 hp_lt hdp hz)
  · -- wrap 支：iv1 < iv（`z` 在 `y` 之前）
    have hv1v : r.idxOf v1 < r.idxOf v := by omega
    have hBform : between r v v1 = r.drop (r.idxOf v + 1) ++ r.take (r.idxOf v1) := by
      rw [betwnTakeDrop hrnd hv1, if_neg h1]
    have hz_y : r.flatten.idxOf z < r.flatten.idxOf y :=
      aqs_flatIdx_lt_of_partIdx_lt hflat hv1 hv hv1v hz hy
    have hp_mem : p ∈ r.drop (r.idxOf v + 1) ++ r.take (r.idxOf v1) := by
      rw [← hBform]
      exact hp
    rcases List.mem_append.mp hp_mem with hpd | hpt
    · -- p 在 drop 支：y 在 d 之前
      have hy_d : r.flatten.idxOf y < r.flatten.idxOf d := by
        have hk1 : r.idxOf v + 1 ≤ r.idxOf p := aqs_idxOf_ge_of_mem_drop hrnd hpd
        exact aqs_flatIdx_lt_of_partIdx_lt hflat hv hp_r (by omega) hy hdp
      exact aqs_mem_betwn_of_idx_wrap hflat hyS hdS hzS hz_y (Or.inl hy_d)
    · -- p 在 take 支：d 在 z 之前
      have hd_z : r.flatten.idxOf d < r.flatten.idxOf z := by
        have hlt1 : r.idxOf p < r.idxOf v1 := aqs_idxOf_lt_of_mem_take hrnd hpt
        exact aqs_flatIdx_lt_of_partIdx_lt hflat hp_r hv1 hlt1 hdp hz
      exact aqs_mem_betwn_of_idx_wrap hflat hyS hdS hzS hz_y (Or.inr hd_z)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aqs_memFlattenBetwnSym
