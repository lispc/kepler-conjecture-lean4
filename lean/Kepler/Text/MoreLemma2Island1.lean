/-
  Kepler.Text.MoreLemma2Island1 — J 战役 J1（M0e 批第一片）：
  37 件 Island-only 重落清单中的 **Tame_list 簇第一组**（链岛重落策略，
  沿用 `rotateTo` 主件的先例；不桥接 TameSpine BEq 世界）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/tame_list.hl`）──
  │ 本片 12 件（HOL 行号 ↔ Spine 现名 ↔ 本文件 Lean 名）：
  │   :1364  `MEM_LAST`             memLastSpine      (TameList2:982)  → memLast
  │   :157   `MEMf_MAP`             memfMap           (TameList2:195)  → memfMap
  │   :13436 `card_le_size`         cardLeSize        (TameList53:164) → cardLeSize
  │   :3872  `uniq_flatten_uniq`    uniqFlattenUniq   (TameList5:319)  → uniqFlattenUniq
  │   :14414 `uniq_flatten_all_uniq` uniqFlattenAllUniq (TameList59:437) → uniqFlattenAllUniq
  │   :11576 `quotient_list_core`   quotientListCore  (TameList34:186) → quotientListCore
  │   :1758  `indexf1`              indexfOne         (TameList3:391)  → indexfOne
  │   :1796  `next_el_indexf`       nextElIndexf      (TameList3:419)  → nextElIndexf
  │   :1840  `next_eln_indexf`      nextElnIndexf     (TameList3:445)  → nextElnIndexf
  │   :1876  `indexf_n`             indexfN           (TameList3:471)  → indexfN
  │   :2859  `next_el_refl`         nextElRefl        (TameList3:1259) → nextElRefl
  │   辅件：`Aq8.MEM_POWER_NEXT_EL` / `Pwssrat.MEM_POWER_NEXT_EL`
  │          memPowerNextEl (JcajyduBetwnBase:138) → memNextElIterate
  │          （indexf 迭代链的前置；M0e 之外顺带覆盖 M0f 清单 #4/#5）
  │ 清单 #19 `indexf_lt_sizel`（:1518）已由 B2 `Reduction4.indexf_lt_length_of_mem`
  │ 逐字覆盖，本片不重落（复用，只记档）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与实例纪律 ──────────────────────────────────────────────
  │ `indexf`/`quotientList`/`core` = `Kepler.Text.Reduction5`（W0，
  │ [DecidableEq α] 烘焙）；`next_el` = `Kepler.Assembly.nextEl`
  │ （[BEq α] 烘焙）；`indexf` 族证明件复用 `TameLp` §10 getD/idxOf
  │ 泛型层（nextEl_eq_getD / getElem_idxOf / nodup_getElem_inj 等）。
  │ **泛型 binder 只用 `[DecidableEq α]`**：Lean core Core.lean:812 由
  │ [DecidableEq α] 导出 BEq/LawfulBEq，故 nextEl/idxOf 全部走派生实例、
  │ synth 唯一（与 Reduction4 头注同一条纪律，不附加 [BEq]/[LawfulBEq]）。
  │ 环安全：imports = Reduction5Base + Reduction4；import 闭包零
  │ `Kepler.Assembly` 主模块、零 `Kepler.Text.TameSpine.*`。
  │ 零 axiom/sorry/admit/native_decide。
  └────────────────────────────────────────────────────────────────

  ┌─ 本片之外的 Tame_list 簇（14 件去向，详见 DELIVERY-M0e）────────
  │ 定义层门槛（L1/L2 DEF-FIX 未落，暂缓）：
  │   :10307 QRDYXYJ_list（marked_list）、:7976 f_list_quotient_alt /
  │   :6687 parts_fst / :6572 parts_uniq_nonnil（normal_list）、
  │   :6522 quotient_all_uniq（marked_list）
  │ parts 机制簇（需链岛重落 partsSpine 递归机，独立片）：
  │   :6334 parts_flatten、:6357 parts_all_nonnil、:6533 parts_nonnil、
  │   :6490 next_el_parts_unlast、:6621 uniq_parts
  │ supermap 簇（须先核 e_list/f_list 定义门槛，独立片）：
  │   :4933 edge_nondeg_f_xor_ni、:6702 f_list_fst_snd、
  │   :4371 is_restricted_e_list_nondeg、:14460 simple_hypermap_uniq
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction4

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2Island1

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (indexf Dart quotientList coreList core)
open Kepler.Text.Reduction4 (indexfRefl indexf_eq_zero indexf_add_sum indexf_add_left
  indexf_lt_length_of_mem)
open Kepler.Text.TameLp (getElem_idxOf getD_eq_getElem_of_lt headD_eq_getD_zero
  nextEl_eq_getD nodup_getElem_inj nextEl_mem_of_mem)
open Kepler.Assembly (nextEl)

/-! ## §1 Mathlib 逐字复用件（tame_list.hl 五件 → 薄别名，零镜像代价） -/

/-- **HOL `MEM_LAST`**（tame_list.hl:1364 `~(s = []) ==> MEM (LAST s) s`）。
Spine 现名 `memLastSpine`（TameList2:982）；本件 = Mathlib `List.getLast_mem`
（Init/Data/List/Lemmas.lean:834 逐字同语句）。 -/
theorem memLast {α : Type*} {s : List α} (h : s ≠ []) : s.getLast h ∈ s :=
  List.getLast_mem h

/-- **HOL `MEMf_MAP`**（tame_list.hl:157 `MEM x u ==> MEM (f x) (MAP f u)`）。
Spine 现名 `memfMap`（TameList2:195）；本件 = Mathlib `List.mem_map_of_mem`
（Init/Data/List/Lemmas.lean:1131）。 -/
theorem memfMap {α β : Type*} {f : α → β} {x : α} {u : List α} (h : x ∈ u) :
    f x ∈ u.map f :=
  List.mem_map_of_mem h

/-- **HOL `card_le_size`**（tame_list.hl:13436 `CARD (set_of_list s) <= sizel s`）。
Spine 现名 `cardLeSize`（TameList53:164，同走 Mathlib `List.toFinset_card_le`，
Mathlib/Data/Finset/Card.lean:209 `#l.toFinset ≤ l.length`）。 -/
theorem cardLeSize {α : Type*} [DecidableEq α] (s : List α) :
    s.toFinset.card ≤ s.length :=
  List.toFinset_card_le s

/-- **HOL `uniq_flatten_uniq`**（tame_list.hl:3872
`uniq (flatten L) /\ MEM s L ==> uniq s`）。
Spine 现名 `uniqFlattenUniq`（TameList5:319）；本件 = Mathlib
`List.nodup_flatten`（Mathlib/Data/List/Nodup.lean:271）的第一个合取项。 -/
theorem uniqFlattenUniq {α : Type*} {L : List (List α)} {s : List α}
    (h1 : L.flatten.Nodup) (h2 : s ∈ L) : s.Nodup :=
  (List.nodup_flatten.mp h1).1 s h2

/-- **HOL `uniq_flatten_all_uniq`**（tame_list.hl:14414
`uniq (flatten s) ==> all uniq s`）。
Spine 现名 `uniqFlattenAllUniq`（TameList59:437）；本件 = Mathlib
`List.nodup_flatten` 的第一个合取项（all 展开为成员量化）。 -/
theorem uniqFlattenAllUniq {α : Type*} {L : List (List α)}
    (h : L.flatten.Nodup) : ∀ s ∈ L, s.Nodup :=
  (List.nodup_flatten.mp h).1

/-! ## §2 `quotient_list_core`（tame_defs2 定义层的展开恒等式） -/

/-- **HOL `quotient_list_core`**（tame_list.hl:11576
`quotient_list L N = MAP (core L) N`）。
Spine 现名 `quotientListCore`（TameList34:186）。
链世界载体：`quotientList L N = coreList (N.map (parts L))`（Reduction5Base:97）、
`core L r = (parts L r).map (fun l => (l.headD (0,0)).1)`（:88）——
本件是 `map` 融合恒等式，`unfold` + `List.map_map` 收口（W0 定义体逐句对齐
tame_defs2.hl:129-136，HOL 侧 `REWRITE_TAC[quotient_list;core_list;core]` 同路）。 -/
theorem quotientListCore (L : fgraph ℕ) (N : List (List Dart)) :
    quotientList L N = N.map (core L) := by
  unfold quotientList coreList core
  rw [List.map_map]
  rfl

/-! ## §3 nextEl 迭代 + indexf 四件链（tame_list.hl:1758-1876/:2859）

核心引擎：`nextEl_eq_getD`（TameLp:4797）把 next_el 归约为
`s.getD ((idxOf x + 1) % len) x`，索引算术走 §3.0 的模长引理。 -/

section IndexfNextElChain

variable {α : Type*} [DecidableEq α]

/-- 模长引擎（私有）：`(b + (n - a)) % n = 1`、`a,b < n` ⇒ `b = (a + 1) % n`。
即 `indexf x y s = 1` 的差值形（B2 `indexf_val` 的 else 分支）反解出
「经回卷的下标后继」。 -/
private theorem idxOf_succ_mod {n a b : ℕ} (ha : a < n) (hb : b < n)
    (h : (b + (n - a)) % n = 1) : b = (a + 1) % n := by
  set v := b + (n - a) with hvdef
  have hn : 0 < n := by omega
  have hv2 : v < 2 * n := by
    rw [hvdef]; omega
  have hv : v = v / n * n + 1 := by
    have h' := Nat.div_add_mod' v n
    omega
  have hq2 : ¬ (2 ≤ v / n) := by
    intro h2
    have hm : 2 * n ≤ v / n * n := Nat.mul_le_mul_right n h2
    omega
  have hqle : v / n ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos (v / n) with hq0 | hqpos
  · rw [hq0, Nat.zero_mul, Nat.zero_add] at hv
    have hb0 : b = 0 := by omega
    have han : a + 1 = n := by omega
    rw [hb0, han, Nat.mod_self]
  · have hq1 : v / n = 1 := by omega
    rw [hq1, Nat.one_mul] at hv
    have hba : b = a + 1 := by omega
    rw [hba, Nat.mod_eq_of_lt (by omega)]

/-- **HOL `MEM_POWER_NEXT_EL`**（Aq8.hl / Pwssrat.hl 同名双章）。
Spine 现名 `memPowerNextEl`（JcajyduBetwnBase:138，私件版本见
TameList3:379 `memNextElIterate`）：next_el 迭代轨道不出表。
indexf 迭代链（:1840/:1876）的前置；顺带覆盖 M0f 清单 #4/#5。 -/
theorem memNextElIterate {s : List α} {x : α} (hx : x ∈ s) :
    ∀ m : ℕ, (nextEl s)^[m] x ∈ s := by
  intro m
  induction m with
  | zero => exact hx
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- **HOL `indexf1`**（tame_list.hl:1758
`MEM x s /\ MEM y s /\ uniq s /\ indexf x y s = 1 ==> next_el s x = y`）。
Spine 现名 `indexfOne`（TameList3:391，BEq 世界版）。
链岛证体：`indexf` 展开得模等式 ⇒ `idxOf_succ_mod` 解出
`idxOf y = (idxOf x + 1) % len` ⇒ `nextEl_eq_getD` + `getElem_idxOf` 收口。 -/
theorem indexfOne {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) (h1 : indexf x y s = 1) :
    nextEl s x = y := by
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hmod : (s.idxOf y + (s.length - s.idxOf x)) % s.length = 1 := by
    unfold indexf at h1
    rw [if_pos (⟨hx, hy⟩ : x ∈ s ∧ y ∈ s)] at h1
    exact h1
  have hiy' : s.idxOf y = (s.idxOf x + 1) % s.length :=
    idxOf_succ_mod hix hiy hmod
  rw [nextEl_eq_getD hx, ← hiy', getD_eq_getElem_of_lt hiy]
  exact getElem_idxOf hy

/-- **HOL `next_el_indexf`**（tame_list.hl:1796
`MEM x s /\ MEM y s /\ uniq s /\ next_el s x = y /\ 1 < sizel s
==> indexf x y s = 1`）。
Spine 现名 `nextElIndexf`（TameList3:419，BEq 世界版）。
链岛证体：`nextEl_eq_getD` 归约后按 `idxOf x + 1` 是否回卷分两支，
`nodup_getElem_inj` 锁 `idxOf y`，模等式收口。 -/
theorem nextElIndexf {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) (hny : nextEl s x = y)
    (hlt : 1 < s.length) : indexf x y s = 1 := by
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hg : s.getD ((s.idxOf x + 1) % s.length) x = y := by
    rw [← nextEl_eq_getD hx]; exact hny
  by_cases hlt2 : s.idxOf x + 1 < s.length
  · have hg' : s[s.idxOf x + 1] = y := by
      rw [Nat.mod_eq_of_lt hlt2, getD_eq_getElem_of_lt hlt2] at hg
      exact hg
    have hiy' : s.idxOf y = s.idxOf x + 1 := by
      have e : s[s.idxOf y] = s[s.idxOf x + 1] :=
        (getElem_idxOf hy).trans hg'.symm
      exact nodup_getElem_inj hnd hiy hlt2 e
    unfold indexf
    rw [if_pos (⟨hx, hy⟩ : x ∈ s ∧ y ∈ s)]
    have e : s.idxOf y + (s.length - s.idxOf x) = s.length + 1 := by
      rw [hiy']; omega
    rw [e, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hlt]
  · have hlast : s.idxOf x = s.length - 1 := by omega
    have hpos : 0 < s.length := by omega
    have hg' : s.headD x = y := by
      have e : (s.idxOf x + 1) % s.length = 0 := by
        rw [hlast, Nat.sub_add_cancel (by omega), Nat.mod_self]
      rw [e, getD_eq_getElem_of_lt hpos] at hg
      rw [headD_eq_getD_zero, getD_eq_getElem_of_lt hpos]
      exact hg
    have h0y : s[0]'hpos = y := by
      rw [← getD_eq_getElem_of_lt hpos x, ← headD_eq_getD_zero]
      exact hg'
    have hz0 : s.idxOf y = 0 := by
      have e4 : s[s.idxOf y] = s[0]'hpos := (getElem_idxOf hy).trans h0y.symm
      exact nodup_getElem_inj hnd hiy hpos e4
    unfold indexf
    rw [if_pos (⟨hx, hy⟩ : x ∈ s ∧ y ∈ s), hz0, hlast]
    have e : 0 + (s.length - (s.length - 1)) = 1 := by omega
    rw [e, Nat.mod_eq_of_lt hlt]

/-- **HOL `next_eln_indexf`**（tame_list.hl:1840
`MEM x s /\ MEM y s /\ uniq s /\ (next_el s POWER n) x = y /\ n < sizel s
==> indexf x y s = n`）。
Spine 现名 `nextElnIndexf`（TameList3:445，BEq 世界版）。
链岛证体：对 `n` 归纳，步进用 `memNextElIterate` + `nextElIndexf` +
`indexf_add_sum`（B2，和界由 `indexf_lt_length_of_mem` 提供）。 -/
theorem nextElnIndexf {m : ℕ} {x y : α} {s : List α}
    (hx : x ∈ s) (hy : y ∈ s) (hnd : s.Nodup) (hp : (nextEl s)^[m] x = y)
    (hlt : m < s.length) : indexf x y s = m := by
  have key : ∀ (k : ℕ) (x' y' : α), x' ∈ s → y' ∈ s → (nextEl s)^[k] x' = y' →
      k < s.length → indexf x' y' s = k := by
    intro k
    induction k with
    | zero =>
      intro x' y' hx' hy' hp' _
      rw [Function.iterate_zero_apply] at hp'
      subst hp'
      exact indexfRefl hy'
    | succ k ih =>
      intro x' y' hx' hy' hp' hlt'
      rw [Function.iterate_succ_apply'] at hp'
      have hk : k < s.length := by omega
      have hym : (nextEl s)^[k] x' ∈ s := memNextElIterate hx' k
      have him : indexf x' ((nextEl s)^[k] x') s = k := ih x' _ hx' hym rfl hk
      have h1yn : indexf ((nextEl s)^[k] x') y' s = 1 :=
        nextElIndexf hym hy' hnd hp' (by omega)
      have hsum := indexf_add_sum hx' hym hy' (by rw [him, h1yn]; omega)
      rw [him, h1yn] at hsum
      exact hsum.symm
  exact key m x y hx hy hp hlt

/-- **HOL `indexf_n`**（tame_list.hl:1876
`MEM x s /\ MEM y s /\ uniq s ==> ((next_el s) POWER (indexf x y s)) x = y`）。
Spine 现名 `indexfN`（TameList3:471，BEq 世界版）。
链岛证体：对 `indexf x y s` 的值归纳；步进 `nextElnIndexf` 给出
`indexf x z = m`，`indexf_add_left`（B2）劈出 `indexf z y = 1`，
`indexfOne` 转回 `nextEl z = y`。 -/
theorem indexfN {x y : α} {s : List α} (hx : x ∈ s) (hy : y ∈ s)
    (hnd : s.Nodup) : (nextEl s)^[indexf x y s] x = y := by
  have hlt := indexf_lt_length_of_mem hx hy
  have key : ∀ m : ℕ, indexf x y s = m → (nextEl s)^[m] x = y := by
    intro m
    induction m with
    | zero =>
      intro h0
      have hxy : x = y := indexf_eq_zero hx hy h0
      subst hxy
      rw [Function.iterate_zero_apply]
    | succ m ih =>
      intro hm
      have hmlt : m < s.length := by omega
      have hym : (nextEl s)^[m] x ∈ s := memNextElIterate hx m
      have him : indexf x ((nextEl s)^[m] x) s = m :=
        nextElnIndexf hx hym hnd rfl hmlt
      have hle : indexf x ((nextEl s)^[m] x) s ≤ indexf x y s := by omega
      have hadd := indexf_add_left hx hym hy hle
      rw [him, hm] at hadd
      have h1 : indexf ((nextEl s)^[m] x) y s = 1 := by omega
      have hny := indexfOne hym hy hnd h1
      rw [Function.iterate_succ_apply', hny]
  exact key _ rfl

/-- **HOL `next_el_refl`**（tame_list.hl:2859
`MEM x s /\ next_el s x = x /\ uniq s ==> s = [x]`）。
Spine 现名 `nextElRefl`（TameList3:1259，BEq 世界版）。
链岛证体：`nextEl_eq_getD` 归约后两支都逼出「相邻下标值相等」，
`nodup_getElem_inj` 反证（回卷支得 `len = 1`），`length_eq_one_iff` 收口。 -/
theorem nextElRefl {s : List α} {x : α}
    (hx : x ∈ s) (h : nextEl s x = x) (hnd : s.Nodup) : s = [x] := by
  have hpos : 0 < s.length := List.length_pos_of_mem hx
  have hix : s.idxOf x < s.length := List.idxOf_lt_length_iff.mpr hx
  have hg : s.getD ((s.idxOf x + 1) % s.length) x = x := by
    rw [← nextEl_eq_getD hx]; exact h
  by_cases hlt : s.idxOf x + 1 < s.length
  · have h1 : s[s.idxOf x] = s[s.idxOf x + 1] := by
      rw [Nat.mod_eq_of_lt hlt, getD_eq_getElem_of_lt hlt] at hg
      exact (getElem_idxOf hx).trans hg.symm
    exact absurd (nodup_getElem_inj hnd hix hlt h1) (by omega)
  · have hlast : s.idxOf x = s.length - 1 := by omega
    have e : (s.idxOf x + 1) % s.length = 0 := by
      rw [hlast, Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [e, getD_eq_getElem_of_lt hpos] at hg
    have h1 : s[s.idxOf x] = s[0]'hpos := (getElem_idxOf hx).trans hg.symm
    have hc := nodup_getElem_inj hnd hix hpos h1
    have hlen : s.length = 1 := by omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
    simp only [List.mem_singleton] at hx
    rw [hx]

end IndexfNextElChain

end Kepler.Text.MoreLemma2Island1

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2Island1.memLast
#print axioms Kepler.Text.MoreLemma2Island1.memfMap
#print axioms Kepler.Text.MoreLemma2Island1.cardLeSize
#print axioms Kepler.Text.MoreLemma2Island1.uniqFlattenUniq
#print axioms Kepler.Text.MoreLemma2Island1.uniqFlattenAllUniq
#print axioms Kepler.Text.MoreLemma2Island1.quotientListCore
#print axioms Kepler.Text.MoreLemma2Island1.memNextElIterate
#print axioms Kepler.Text.MoreLemma2Island1.indexfOne
#print axioms Kepler.Text.MoreLemma2Island1.nextElIndexf
#print axioms Kepler.Text.MoreLemma2Island1.nextElnIndexf
#print axioms Kepler.Text.MoreLemma2Island1.indexfN
#print axioms Kepler.Text.MoreLemma2Island1.nextElRefl
