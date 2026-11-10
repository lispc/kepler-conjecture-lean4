/-
  Kepler.Text.Reduction5J5CoreNextF — J5-1c 段（chain 载体）：
  `f_list_imp_last`（reduction4.hl:1609）+ `next_el_core_imp_next_f`（:4847）
  ——next_el_core 三件收官（前两件见 Reduction5J5CoreLast）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ reduction4.hl:1609 `f_list_imp_last`（38L）→ `fListImpLast`：
  │   good_list ∧ x ∈ list_of_darts L ∧ is_edge_nondegenerate ∧ uniq r ∧
  │   r ≠ [] ∧ x ∈ r ∧ next_el r x = f_list L x ⇒ x ∈ MAP LAST (parts L r)
  │ reduction4.hl:4847 `next_el_core_imp_next_f`（50L）→ `nextElCoreImpNextF`：
  │   （next_el_core_imp_eq_last 的全部前件）∧ next_el r' y = f_list L y
  │   ⇒ next_el r y = f_list L y
  │ 证（与 HOL 同构）：
  │ · f_list_imp_last：x 的原子 p（parts_flatten → partsMemExists）；
  │   若 x ≠ LAST p：`next_el_parts_unlast`（next_el r x = next_el p x）+
  │   `parts_next_unlast`（next_el p x = f_list L (e_list x)）⇒
  │   f_list L x = f_list L (e_list x)，与 `edge_nondeg_f_xor_ni` 矛盾；
  │ · imp_next_f：`next_el_core_imp_eq_last` ⇒ LAST p = LAST p'；
  │   `f_list_imp_last` 于 (r', y) ⇒ y 为某原子 q 的末元，`uniq_sublist_unique`
  │   ⇒ q = p' ⇒ LAST p' = y；`normal_list_parts_next_last` 于 (r, p) 收口。
  └────────────────────────────────────────────────────────────────

  ┌─ 语义查重记档（工单要求：别只按名）───────────────────────────────
  │ `f_list_imp_last` 树内确缺：其两条直接支件
  │ `partsNextUnlast`（MoreLemma2PartsFst:221）/ `nextElPartsUnlast`
  │ （MoreLemma2Island3:390）均在库，但「MEM x (MAP LAST parts)」合成件
  │ 无落点（按名 fListImpLast/f_list_imp_last 零命中；按结论形
  │ `∈ (parts …).map` + getLast! 检索亦无同陈述件）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓双零写入；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5CoreLast

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList eList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList loopList)

/-- 非空表 `getLast!` 是成员（CoreLast 私件同证重推导）。 -/
private theorem getLastBangMemNF {l : List Dart} (h : l ≠ []) : l.getLast! ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.getLast_mem (List.cons_ne_nil a t)

/-- **HOL `f_list_imp_last`**（reduction4.hl:1609）：
`next_el r x = f_list L x ⇒ x` 是某原子的末元。 -/
theorem fListImpLast (L : fgraph ℕ) (hL : GoodList L)
    (hen : (hypermapOfList L hL).EdgeNondegenerate)
    {r : List Dart} (hrnd : r.Nodup) (hrne : r ≠ []) {x : Dart}
    (hxD : x ∈ listOfDarts L) (hx : x ∈ r) (hnext : nextEl r x = fList L x) :
    x ∈ (parts L r).map (fun p => p.getLast!) := by
  obtain ⟨p, hp, hxp⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hx
  by_cases hlast : x = p.getLast!
  · exact List.mem_map.mpr ⟨p, hp, hlast.symm⟩
  · exfalso
    have h1 : nextEl r x = nextEl p x :=
      Kepler.Text.MoreLemma2Island3.nextElPartsUnlast L hrnd hrne hp hxp hlast
    have h2 : nextEl p x = fList L (eList x) :=
      Kepler.Text.MoreLemma2PartsFst.partsNextUnlast L hrnd hrne p hp x hxp hlast
    exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL hen hxD
      (hnext.symm.trans (h1.trans h2))

/-- **HOL `next_el_core_imp_next_f`**（reduction4.hl:4847）：
y 同落两 loop 的原子 p / p'、core 环后继一致、且 y 在 r' 上走 f 支
⇒ y 在 r 上也走 f 支。 -/
theorem nextElCoreImpNextF (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (hen : (hypermapOfList L hL).EdgeNondegenerate)
    {N : List (List Dart)} (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    {p : List Dart} (hp : p ∈ parts L r) (hcu : (core L r).Nodup)
    {N' : List (List Dart)} (hN' : normalList L hL N') {r' : List Dart} (hr' : r' ∈ N')
    {p' : List Dart} (hp' : p' ∈ parts L r') (hcu' : (core L r').Nodup)
    {y : Dart} (hy : y ∈ p) (hy' : y ∈ p')
    (hnext : nextEl (core L r) y.1 = nextEl (core L r') y.1)
    (hf' : nextEl r' y = fList L y) :
    nextEl r y = fList L y := by
  have heq : p.getLast! = p'.getLast! :=
    nextElCoreImpEqLast L hL hgn hunL hen hN hr hp hcu hN' hr' hp' hcu' hy hy' hnext
  obtain ⟨hr'nd, hr'ne, _, _, hsub'⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN' hr' hp'
  have hyr' : y ∈ r' := hsub' y hy'
  have hyD : y ∈ listOfDarts L := ((hN'.2.2.2.1 r' hr') y hyr').1
  -- LAST p' = y
  obtain ⟨q, hq, hql⟩ :=
    List.mem_map.mp (fListImpLast L hL hen hr'nd hr'ne hyD hyr' hf')
  obtain ⟨_, _, _, hqne, _⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hN' hr' hq
  have hyq : y ∈ q := by
    have h := getLastBangMemNF hqne
    rwa [hql] at h
  have hpf' : (parts L r').flatten = r' :=
    Kepler.Text.MoreLemma2Island2.partsFlatten L hr'nd hr'ne
  have hqp' : q = p' :=
    Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L r')
      (by rw [hpf']; exact hr'nd) q hq p' hp' ⟨y, hyq, hy'⟩
  have hlast' : p'.getLast! = y := by rw [← hqp']; exact hql
  -- normal_list_parts_next_last 于 (r, p)
  have h := Kepler.Text.MoreLemma2QuotientAlt.normalListPartsNextLast L hL hN hr hp
  rw [heq, hlast'] at h
  exact h

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.fListImpLast
#print axioms Kepler.Text.Reduction5.nextElCoreImpNextF
