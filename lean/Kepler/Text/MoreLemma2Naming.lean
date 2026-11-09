/-
  Kepler.Text.MoreLemma2Naming — J 战役 J1（M0f 批）：命名章簇链岛重落。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/`）──────────────
  │ 本批 8 件（HOL 锚 ↔ Spine 现名 ↔ 本文件 Lean 名）：
  │   AQ23.hl:221        `LAST_FLATTEN_2`      lastFlatten2  (JcajyduBetwnBase:172) → lastFlatten2
  │   AQ4.hl:383         `next_el_last_hd`     nextElLastHd  (JcajyduBetwnBase:185) → nextElLastHd
  │   AQ4.hl:398         `prev_el_last_hd`     prevElLastHd  (JcajyduBetwnBase:201) → prevElLastHd
  │   AQ8.hl:88          `parts_mem_exists`    partsMemExists (JcajyduBetwnMap:72) → partsMemExists
  │   DANGEYJ.hl:616     `mem_imp_not_nil`     mem_imp_not_nil (TameList71:493) → memImpNotNil
  │   HOJODCM.hl:49      `ytrans_mem_rtrans_v0` ytransMemRtrans (JcajyduAqTowerBase:195) → ytransMemRtrans
  │   hypermap.hl:496    `LE_SUC_PRE`          （Spine 异名于 TameList62 段）→ leSucPre
  │   list_hypermap-compiled.hl:563
  │                      `uniq_sublist_unique` uniqSublistUnique (TameList6:604) → uniqSublistUnique
  │ 清单 #4/#5（Aq8/Pwssrat `MEM_POWER_NEXT_EL`）已由 M0e
  │ `MoreLemma2Island1.memNextElIterate` 覆盖，不重落。
  │ 清单 #37（Reduction3.AQIUNPP 三件）：**停报**——其陈述以
  │ `transform_assumption_v2 L` 为前提，该槽在链世界**未定义**
  │ （Reduction3Thm2.lean 头注「transform_assumption_v2 的无条件形树内
  │ 未落（缺口 A）」；J2 领土），等 J2 落库后按假设驱动件补。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体 ────────────────────────────────────────────────────────
  │ `last_flatten_2`/`next_el`/`prev_el` 走 `List.getLast`/`nextEl`/
  │ `prevEl`（HOL `HD` junk ↦ Lean 显式缺省参 `headD x`，逐件记档）；
  │ `parts_mem_exists` 走链岛 `parts`（Reduction5Base:75）+
  │ `MoreLemma2Island2.partsFlatten`；`ytrans_mem_rtrans_v0` 走
  │ `ytrans_def`/`rtrans_zero`（Reduction5）+ `markedList` 合取 6
  │ （ChainListsL2:118）+ `MoreLemma2Aux.minNotEqImpEq`（M0a）+
  │ `MoreLemma2Island1.memNextElIterate`（M0e）。
  │ 实例纪律：泛型件只用 `[DecidableEq α]`（nextEl/idxOf 走导出实例）；
  │ 缺省值用显式 `x : α` 参数（`headD x`）而非 `[Inhabited]`。
  │ 零 axiom/sorry/admit/native_decide；import 闭包零 TameSpine/Assembly 主模块。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Aux
import Kepler.Text.ChainListsL2

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2Naming

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart parts ytrans rtrans finalList ytrans_def rtrans_zero
  minNum minNum_spec)
open Kepler.Text.MoreLemma2Island1 (memNextElIterate)
open Kepler.Text.MoreLemma2Island2 (partsFlatten)
open Kepler.Text.MoreLemma2Aux (minNotEqImpEq)
open Kepler.Text.ChainLists (markedList)
open Kepler.Assembly (fList eList nextEl prevEl GoodList)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt idxOf_getElem
  getElem_idxOf)

/-! ## §1 纯 list / 算术件（3 件） -/

/-- **HOL `LAST_FLATTEN_2`**（AQ23.hl:221）
`~(r = []) ∧ ~(LAST r = []) ==> LAST (flatten r) = LAST (LAST r)`。
Spine 现名 `lastFlatten2`（JcajyduBetwnBase:172）。
证体：`dropLast_append_getLast` 尾分解 + `getLast_append_of_ne_nil`。 -/
theorem lastFlatten2 {α : Type*} {r : List (List α)} (hne : r ≠ [])
    (hlne : r.getLast hne ≠ []) (hflatne : r.flatten ≠ []) :
    r.flatten.getLast hflatne = (r.getLast hne).getLast hlne := by
  have hf : r.flatten = r.dropLast.flatten ++ r.getLast hne := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.flatten_append, List.flatten_singleton]
  have hlift : (r.dropLast.flatten ++ r.getLast hne) ≠ [] := by
    rw [← hf]; exact hflatne
  have hget2 : r.flatten.getLast hflatne
      = (r.dropLast.flatten ++ r.getLast hne).getLast hlift :=
    List.getLast_congr hflatne hlift hf
  rw [hget2, List.getLast_append_of_ne_nil _ hlne]

/-- **HOL `LE_SUC_PRE`**（hypermap.hl:496 `!n:num. 1 <= n ==> SUC(PRE n) = n`）。
纯算术（`PRE n = n - 1`）。 -/
theorem leSucPre {n : ℕ} (h : 1 ≤ n) : Nat.succ (n - 1) = n := by omega

/-- **HOL `mem_imp_not_nil`**（DANGEYJ.hl:616 `!s x. MEM x s ==> ~(s = [])`）。
Spine 现名 `mem_imp_not_nil`（TameList71:493）。 -/
theorem memImpNotNil {α : Type*} {s : List α} {x : α} (h : x ∈ s) : s ≠ [] :=
  List.ne_nil_of_mem h

/-! ## §2 next_el / prev_el 末元回卷件（2 件）

HOL `HD h` 的 junk 值在 Lean 以显式缺省参 `x` 承载（`h.headD x`）：
`h ≠ []` 前提下两库逐值一致（空表支不可达，记档）。 -/

/-- **HOL `next_el_last_hd`**（AQ4.hl:383
`uniq h ∧ ~(h = []) ==> next_el h (LAST h) = HD h`）。
Spine 现名 `nextElLastHd`（JcajyduBetwnBase:185）。
证体：`indexl LAST`（`idxOf_getElem`）+ 回卷模 `Nat.mod_self`。 -/
theorem nextElLastHd {α : Type*} [DecidableEq α] {h : List α} {x : α}
    (hnd : h.Nodup) (hne : h ≠ []) :
    nextEl h (h.getLast hne) = h.headD x := by
  have hpos : 0 < h.length := List.length_pos_of_ne_nil hne
  have hmem : h.getLast hne ∈ h := List.getLast_mem hne
  have hidx : h.idxOf (h.getLast hne) = h.length - 1 := by
    rw [List.getLast_eq_getElem hne]
    exact idxOf_getElem hnd (by omega)
  have he : h.length - 1 + 1 = h.length := by omega
  rw [nextEl_eq_getD hmem, hidx, he, Nat.mod_self,
    getD_eq_getElem_of_lt hpos (h.getLast hne)]
  cases h with
  | nil => exact absurd hne (by simp)
  | cons a t => rfl

/-- 非空表 `getLastD` = `getLast`（priv；prev_el_last_hd 的缺省吸收件）。 -/
private theorem getLastD_eq_getLast {α : Type*} {l : List α} {d : α} (h : l ≠ []) :
    l.getLastD d = l.getLast h := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil h]
  simp

/-- **HOL `prev_el_last_hd`**（AQ4.hl:398
`uniq h ∧ ~(h = []) ==> prev_el h (HD h) = LAST h`）。
Spine 现名 `prevElLastHd`（JcajyduBetwnBase:201）。
证体：`prevEl` 展开 + `indexl (HD h) = 0`（`List.idxOf_cons_self`）+
`getLastD_eq_getLast` 缺省吸收。 -/
theorem prevElLastHd {α : Type*} [DecidableEq α] {h : List α} {x : α}
    (hnd : h.Nodup) (hne : h ≠ []) :
    prevEl h (h.headD x) = h.getLast hne := by
  cases h with
  | nil => exact absurd rfl hne
  | cons a t =>
    have hhead : (a :: t).headD x = a := by rw [List.headD_cons]
    have hmem : (a :: t).headD x ∈ a :: t := by
      rw [hhead]; exact List.mem_cons_self
    have h0 : (a :: t).idxOf ((a :: t).headD x) = 0 := by
      rw [hhead]
      exact List.idxOf_cons_self (l := t)
    rw [prevEl, if_neg (by simp), if_pos h0]
    exact getLastD_eq_getLast (l := a :: t) (d := (a :: t).headD x)
      (List.cons_ne_nil a t)

/-! ## §3 parts 成员 / 子表唯一件（2 件） -/

/-- **HOL `parts_mem_exists`**（AQ8.hl:88
`uniq r ∧ MEM x r ==> ?p. MEM p (parts L r) ∧ MEM x p`）。
Spine 现名 `partsMemExists`（JcajyduBetwnMap:72）。
证体：`partsFlatten` 把 `x ∈ r` 转进 `(parts L r).flatten`，
`List.mem_flatten` 取出 atom 见证。 -/
theorem partsMemExists (L : fgraph ℕ) {r : List Dart} {x : Dart}
    (hun : r.Nodup) (hx : x ∈ r) :
    ∃ p ∈ parts L r, x ∈ p := by
  have hne : r ≠ [] := List.ne_nil_of_mem hx
  have hmem : x ∈ (parts L r).flatten := by
    rw [partsFlatten L hun hne]; exact hx
  exact List.mem_flatten.mp hmem

/-- **HOL `uniq_sublist_unique`**（list_hypermap-compiled.hl:563
`uniq (flatten L) ∧ MEM l1 L ∧ MEM l2 L ∧ MEM x l1 ∧ MEM x l2 ==> l1 = l2`）。
Spine 现名 `uniqSublistUnique`（TameList6:604）。
证体：flatten-cons 分解 + `nodup_append` 两段不交排除跨表支。 -/
theorem uniqSublistUnique {α : Type*} :
    ∀ (N : List (List α)), N.flatten.Nodup → ∀ s ∈ N, ∀ t ∈ N,
      (∃ d, d ∈ s ∧ d ∈ t) → s = t := by
  intro N
  induction N with
  | nil => intro _ s hs; exact absurd hs (by simp)
  | cons u N' ih =>
    intro hfl s hs t ht hd
    rw [List.flatten_cons, List.nodup_append] at hfl
    obtain ⟨hu, hN'fl, hdisj⟩ := hfl
    have hd' : ∀ x ∈ u, x ∉ N'.flatten := fun x hx hmem =>
      (hdisj x hx x hmem) rfl
    obtain ⟨d, hds, hdt⟩ := hd
    rcases List.mem_cons.mp hs with rfl | hs'
    · rcases List.mem_cons.mp ht with rfl | ht'
      · rfl
      · have hf : d ∈ N'.flatten := List.mem_flatten.mpr ⟨t, ht', hdt⟩
        exact absurd hf (hd' d hds)
    · rcases List.mem_cons.mp ht with rfl | ht'
      · have hf : d ∈ N'.flatten := List.mem_flatten.mpr ⟨s, hs', hds⟩
        exact absurd hf (hd' d hdt)
      · exact ih hN'fl s hs' t ht' ⟨d, hds, hdt⟩

/-! ## §4 AQ 塔成员件（1 件；J2 前的假设驱动形） -/

/-- `min_not_eq_imp_eq` 的 **POWER 形**重述（私有）：`Nat.iterate` 的
右嵌套使 `f^[m+2] x = f (f^[m] x)` 非定义等（Toolchain 语义
`f^[n+1] x = f^[n] (f x)`），M0a 的 `f (f (f^[m] x))` 形与 `lm`/`ly`
的 `f^[m+2]` 形不能 rfl 衔接——本件按 lm 定义形直接重证（同 M0a 证体，
hgood 支直接用 pow 形）。 -/
private theorem minNotEqImpEqPow {α : Type*} (f g : α → α) (x : α) {n : ℕ}
    (h : minNum {m : ℕ | (f^[m + 2]) x ≠ g ((f^[m + 1]) x)} = n) :
    ∀ i, i ≤ n → (f^[i + 1]) x = (g^[i]) (f x) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp
  | succ i ih =>
    intro hi
    have hi' : i ≤ n := by omega
    have hprev := ih hi'
    have hgood : (f^[i + 2]) x = g ((f^[i + 1]) x) := by
      by_contra hbad
      have hmem : i ∈ {m : ℕ | (f^[m + 2]) x ≠ g ((f^[m + 1]) x)} := hbad
      have hle : n ≤ i := h ▸ (minNum_spec ⟨i, hmem⟩).2 i hmem
      omega
    calc (f^[i + 1 + 1]) x = (f^[i + 2]) x := rfl
      _ = g ((f^[i + 1]) x) := hgood
      _ = g ((g^[i]) (f x)) := by rw [← hprev]
      _ = (g^[i + 1]) (f x) := (Function.iterate_succ_apply' g i (f x)).symm

/-- **HOL `ytrans_mem_rtrans_v0`**（HOJODCM.hl:49
`good_list L ∧ good_list_nodes L ∧ marked_list L N r x ∧ ~(final_list L r)
==> MEM (ytrans L N r x 0) r`）。
Spine 现名 `ytransMemRtrans`（JcajyduAqTowerBase:195）。
链岛证体：`ytrans_def`+`rtrans_zero` 归约到 `ly`；`minNotEqImpEq`（M0a）
把 `f_list` 幂改成 `next_el` 幂（只用 marked_list 合取 6 的点态
`next_el r x = f_list L x`）；`x ∈ r`（合取 4）产出后收
`memNextElIterate`（M0e）。注：mark 的 `good_list_nodes L` 来自 hL/hgn
载体入参；`~(final_list L r)` 前提 HOL 证体未消费，逐字保留。 -/
theorem ytransMemRtrans (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hm : markedList L hL N r x) (hf : ¬ finalList L r) :
    ytrans L N r x 0 ∈ r := by
  have hnext : fList L x = nextEl r x := (hm.2.2.2.2.2.1).symm
  have hx : x ∈ r := hm.2.2.2.1
  have hlY : Kepler.Text.Reduction5.ly L r x
      = (nextEl r)^[Kepler.Text.Reduction5.lm L r x + 1] x := by
    have hmin := minNotEqImpEqPow (nextEl r) (fList L) x
      (n := Kepler.Text.Reduction5.lm L r x) rfl
    unfold Kepler.Text.Reduction5.ly
    rw [Function.iterate_succ_apply, hnext]
    exact (hmin (Kepler.Text.Reduction5.lm L r x) (Nat.le_refl _)).symm
  have hmem : ∀ k : ℕ, (nextEl r)^[k] x ∈ r := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Kepler.Text.TameLp.nextEl_mem_of_mem ih
  rw [ytrans_def, rtrans_zero, hlY]
  exact hmem _

end Kepler.Text.MoreLemma2Naming

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2Naming.lastFlatten2
#print axioms Kepler.Text.MoreLemma2Naming.leSucPre
#print axioms Kepler.Text.MoreLemma2Naming.memImpNotNil
#print axioms Kepler.Text.MoreLemma2Naming.nextElLastHd
#print axioms Kepler.Text.MoreLemma2Naming.prevElLastHd
#print axioms Kepler.Text.MoreLemma2Naming.partsMemExists
#print axioms Kepler.Text.MoreLemma2Naming.uniqSublistUnique
#print axioms Kepler.Text.MoreLemma2Naming.ytransMemRtrans
