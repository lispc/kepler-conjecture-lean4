/-
  Kepler.Text.Reduction5J5CoreLast — J5-1b 段（chain 载体）：
  next_el_core 三件之二——`next_el_core_last`（reduction4.hl:4773）+
  `next_el_core_imp_eq_last`（:4809）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ reduction4.hl:4773 `next_el_core_last`（36L）→ `nextElCoreLast`：
  │   good_list ∧ good_list_nodes ∧ all uniq L ∧ is_edge_nondegenerate ∧
  │   uniq (core L r) ∧ normal_list L N ∧ r ∈ N ∧ p ∈ parts L r
  │   ⇒ next_el (core L r) (FST (LAST p)) = SND (LAST p)
  │ reduction4.hl:4809 `next_el_core_imp_eq_last`（38L）→ `nextElCoreImpEqLast`：
  │   两套 (N,r,p)/(N',r',p') 前件 ∧ y ∈ p ∧ y ∈ p' ∧
  │   next_el (core L r) (FST y) = next_el (core L r') (FST y) ⇒ LAST p = LAST p'
  │ 证（与 HOL 同构）：
  │ · last：`next_core_FST_SYM`（J5-1a `nextCoreFstSym`）于 d := LAST p——
  │   `normal_list_parts_next_last`（MoreLemma2QuotientAlt，已落）供
  │   f_list L (LAST p) = next_el r (LAST p)；`parts_uniq_nonnil`
  │   （Island3，已落）供 LAST p ∈ r；`f_list_fst_snd`（Island3）收口；
  │ · imp_eq_last：`parts_fst` 把 FST (LAST p)/FST (LAST p') 都换成 FST y，
  │   last 两次 + 假设 ⇒ SND 相等 ⇒ 对组相等。
  └────────────────────────────────────────────────────────────────

  ┌─ 范围记账 ─────────────────────────────────────────────────────
  │ 三件之三 `next_el_core_imp_next_f`（:4847）吃 `f_list_imp_last`
  │ （reduction4.hl:1609，38L，树内按名零命中）——冻结（DELIVERY_j51b §3）；
  │ `bet_eq_nil_imp_next_z_y`（:4970）吃 `Aq1.uniq_fst_split_norm`
  │ （AQ1.hl:1373，**未落**——JcajyduAqSplit1B 未了清单在案，前置
  │ uniq_flatten_map_upt_betwn/node_betwn_not_in_rtrans/betwn_not_in_fst_flatten
  │ 同批未落）——冻结；`bet_eq_nil_imp_next_y_z`（:4897）**不吃**该件
  │ （证体消费 rtrans1/trans_add/transform_count_not/AQIUNPP/split_normal_list
  │ 展开/ytran_me_f/next_el_last_hd），本笔未施工（同表）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓双零写入；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.MoreLemma2QuotientAlt

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList loopList)

/-- 非空表 `getLast!` 是成员。 -/
private theorem getLastBangMemCL {l : List Dart} (h : l ≠ []) : l.getLast! ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.getLast_mem (List.cons_ne_nil a t)

/-- **HOL `next_el_core_last`**（reduction4.hl:4773）：
`next_el (core L r) (FST (LAST p)) = SND (LAST p)`。 -/
theorem nextElCoreLast (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (hen : (hypermapOfList L hL).EdgeNondegenerate)
    {N : List (List Dart)} (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    (hcu : (core L r).Nodup) {p : List Dart} (hp : p ∈ parts L r) :
    nextEl (core L r) (p.getLast!).1 = (p.getLast!).2 := by
  obtain ⟨hrnd, hrne, hpnd, hpne, hsub⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN hr hp
  have hlr : p.getLast! ∈ r := hsub _ (getLastBangMemCL hpne)
  have hfl : fList L (p.getLast!) = nextEl r (p.getLast!) :=
    (Kepler.Text.MoreLemma2QuotientAlt.normalListPartsNextLast L hL hN hr hp).symm
  have hlD : p.getLast! ∈ listOfDarts L := ((hN.2.2.2.1 r hr) _ hlr).1
  rw [nextCoreFstSym L hL hen hgn hN hr hlr hfl hcu, ← hfl]
  exact Kepler.Text.MoreLemma2Island3.fListFstSnd L hunL hlD

/-- **HOL `next_el_core_imp_eq_last`**（reduction4.hl:4809）：
同一 dart y 落在两个 loop 的原子 p / p' 中，且 core 环后继一致 ⇒ `LAST p = LAST p'`。 -/
theorem nextElCoreImpEqLast (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (hen : (hypermapOfList L hL).EdgeNondegenerate)
    {N : List (List Dart)} (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    {p : List Dart} (hp : p ∈ parts L r) (hcu : (core L r).Nodup)
    {N' : List (List Dart)} (hN' : normalList L hL N') {r' : List Dart} (hr' : r' ∈ N')
    {p' : List Dart} (hp' : p' ∈ parts L r') (hcu' : (core L r').Nodup)
    {y : Dart} (hy : y ∈ p) (hy' : y ∈ p')
    (hnext : nextEl (core L r) y.1 = nextEl (core L r') y.1) :
    p.getLast! = p'.getLast! := by
  obtain ⟨_, _, _, hpne, _⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN hr hp
  obtain ⟨_, _, _, hp'ne, _⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN' hr' hp'
  have hl1 : (p.getLast!).1 = y.1 := by
    rw [Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hr hp (getLastBangMemCL hpne),
      Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hr hp hy]
  have hl1' : (p'.getLast!).1 = y.1 := by
    rw [Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN' hr' hp' (getLastBangMemCL hp'ne),
      Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN' hr' hp' hy']
  have h2 := nextElCoreLast L hL hgn hunL hen hN hr hcu hp
  have h2' := nextElCoreLast L hL hgn hunL hen hN' hr' hcu' hp'
  rw [hl1] at h2
  rw [hl1'] at h2'
  have hsnd : (p.getLast!).2 = (p'.getLast!).2 := by
    rw [← h2, ← h2', hnext]
  exact Prod.ext (hl1.trans hl1'.symm) hsnd

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.nextElCoreLast
#print axioms Kepler.Text.Reduction5.nextElCoreImpEqLast
