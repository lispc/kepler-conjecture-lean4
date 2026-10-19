/-
  Kepler.Text.TameSpine.TameList39 — B1 Tame_list 地基批 39：parts 章
  归纳主体（tamespine-port-plan §4 批次表 B1 行；接续批 38 =
  TameList38.lean，批 38 终点 = HOL :11944；本批起点 = HOL :11946
  `parts_characterize`。行号均按主仓 reference/flyspeck（commit 1ce0353）
  实测。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11946-:12106）：

  主件：`parts_characterize` :11946-:12106
  `!L r prt. ~(r=[]) /\ uniq r /\ (flatten prt = r) /\
  all (\p. ~(p=[])) prt /\
  (!p d. MEM p prt /\ MEM d p /\ ~(d = LAST r) ==>
  (~(next_el r d = f_list L (e_list d)) <=> d = LAST p)) ==>
  parts L r = prt`
  ↦ `partsCharacterize`（真证）。HOL 证体 size_induct 归纳 + parts_cases
  二分支：闭分支 parts_pure 得 parts L r = [r]，prt 逐层拆（[] 爆
  flatten prt = [] 与 ~r=[] 矛盾；[h] 经 flatten [h] = h 得 h = r；
  h::h'::t' 爆——LAST h ∈ h 且 LAST h = LAST r ⇒ LAST h ∈ h' ++ flatten
  t'，Seq2.mem_imp_not_uniq_cat 杀 uniq r）；裂分支 r = cat u v 上
  cat_from 把 prt 在含 LAST u 的件 p 处二分（prt = cat a b，LAST a = p），
  主假设在 (p, LAST u) 槽（d ≠ LAST r 由 uniq (cat u v) 供）经裂支假设
  next_el r (LAST u) ≠ f_list L (e_list (LAST u)) 换出 LAST u = LAST p，
  last_flatten 得 LAST (flatten a) = LAST u，eqseq_cat3 收 flatten a = u
  /\ flatten b = v，IH 双发 + parts_cat 收口（两侧逐件假设经
  next_el_cat1/2 把 next_el r 换面 next_el u/v）。

  parts 定义层折算盘点（批 38 头注预记「疑需新章 def 层镜像」勘误）：
  parts = partition_into_atom (f_list L o e_list) r
  （tame_defs2.hl:126-127），Lean 载体全数在库、零新 def——
  - `partition_into_atom0`（tame_defs2.hl:112-116）= 批 7
    partitionIntoAtom0（TameList7.lean:446）；`partition_into_atom`
    = 批 7 partitionIntoAtom（TameList7.lean:457）；
  - `parts` ↦ 批 7 partsSpine（TameList7.lean:462，逐字）；
  - `partition_into_atom0r` 机制块（tame_list.hl:6007-:6020）= 批 9
    partitionIntoAtom0r/partitionIntoAtom0rCases（TameList9.lean:676/:682）；
  - `parts_pure` :6111 = 批 9 partsPure（TameList9.lean:817）；
  - `parts_cat` :6253 = 批 9 partsCat（TameList9.lean:1030）；
  - `parts_cases` :6273 = 批 9 partsCases（TameList9.lean:1045）；
  - `size_induct` :6296 = 批 9 sizeInduct（TameList9.lean:859）；
  - `parts_induct_lemma` :6315 = 批 9 partsInductLemma
    （TameList9.lean:878）；
  - `cat_from` :5959 = 批 9 catFrom（TameList9.lean:441）；
  - `next_el_cat1` :5613 / `next_el_cat2` :5648 = 批 9 nextElCat1/
    nextElCat2（TameList9.lean:199/:248）；
  - `eqseq_cat3` :11879 = 批 38 eqseqCat3（TameList38.lean 收口件）；
  - `Seq.size_cat` = List.length_append、`Seq.all_cat`/`Seq.allP` =
    mem_append/mem 逐点、`Seq.mem_flatten` = Mathlib List.mem_flatten、
    `flatten_eq_nil` :11906 / `last_flatten` :11922 = 批 37 已收（但
    特化 List (List ℕ)，本批私件同证重推导 ℕ × ℕ 面）。
    系批 38 侦察面漏（对拍 TameList7/9 头注即见，批 34-38 连续第 3 批
    同型勘误），本批更正记档，零新载体落地。

  新落地载体：`Seq2.mem_imp_not_uniq_cat`
  （tame/ssreflect/seq2-compiled.hl:366-:371，
  `MEM x l1 /\ MEM x l2 ==> ~(uniq (cat l1 l2))`）↦ memImpNotUniqCat
  （真证，nodup_append 三段一投）。

  私件（惯例同证重推导，非新领土）：getLast!_eq_getLast/getLastMem
  （批 37/9 同证，泛型 α 面）、flatten_eq_nil/last_flatten 的
  ℕ × ℕ 面（批 37 同证重定型）。

  诚实记账：主件 + 新载体件全真证，零新 def、零 sorry、零止损件、
  零记账债。红线遵守：零既有文件触碰、零 git 写操作。
  批 40 接续点：HOL :12108 `iso_list_parts`（parts_characterize 首个
  消费者；需侦察 normal_list_uniq_nonnil/inj_on_dart_of_list/lower_case/
  map_inj_in_uniq/MAP_flatten 载体面 + 批 16 quotient 章桥件）。
-/

import Kepler.Text.TameSpine.TameList38

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList)
open Kepler.Graphs (fgraph)

/-! ### §1 新载体件（HOL seq2-compiled.hl:366 mem_imp_not_uniq_cat） -/

/-- **HOL `Seq2.mem_imp_not_uniq_cat`**（seq2-compiled.hl:366-:373）
`MEM x l1 /\ MEM x l2 ==> ~(uniq (cat l1 l2))`——nodup_append 第三段
直接投影（x 同时居于两半即非 uniq）。 -/
theorem memImpNotUniqCat {l1 l2 : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (h1 : x ∈ l1) (h2 : x ∈ l2) : ¬(l1 ++ l2).Nodup :=
  fun h => absurd rfl ((List.nodup_append.mp h).2.2 x h1 x h2)

/-! ### §2 私件（批 37/9 同证重推导，非新领土） -/

/-- 非空表 `getLast!` = `getLast`（批 37 私件同证重推导）。 -/
private theorem getLast!EqGetLast' {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! = l.getLast h := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  simp

/-- 非空表 `getLast!` 必是成员（批 9/37 私件同证重推导）。 -/
private theorem getLastMem' {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rw [List.getLast!_cons_eq_getLastD]; exact List.getLastD_mem_cons

/-- **HOL `flatten_eq_nil`**（tame_list.hl:11906，批 37 同证重定型
`List (List (ℕ × ℕ))` 面）`flatten r = [] <=> all (\p. p = []) r`。 -/
private theorem flattenEqNilPair (t : List (List (ℕ × ℕ))) :
    t.flatten = [] ↔ ∀ p ∈ t, p = [] := by
  constructor
  · intro h p hp
    by_contra hpne
    obtain ⟨x, hxp⟩ := List.exists_mem_of_ne_nil p hpne
    have hx : x ∈ t.flatten := List.mem_flatten.mpr ⟨p, hp, hxp⟩
    rw [h] at hx
    exact List.not_mem_nil hx
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil t.flatten hne
    obtain ⟨j, hj, hxp⟩ := List.mem_flatten.mp hx
    rw [h j hj] at hxp
    exact absurd hxp (by simp)

/-- **HOL `cat_from`**（tame_list.hl:5959-:5975，批 9 catFrom 同证重定型
`List (List (ℕ × ℕ))` 面——HOL cat_from 本为多态，本批在件表层消费）
`MEM x s ==> (?a b. s = cat a b /\ x = LAST a /\ ~(a = []))`。 -/
private theorem catFromPair {x : List (ℕ × ℕ)} {s : List (List (ℕ × ℕ))}
    (hx : x ∈ s) :
    ∃ a b : List (List (ℕ × ℕ)), s = a ++ b ∧ a.getLast! = x ∧ a ≠ [] := by
  obtain ⟨a, b, hab⟩ := List.append_of_mem (List.mem_reverse.mpr hx)
  have key : (a ++ x :: b).reverse = (b.reverse ++ [x]) ++ a.reverse := by
    rw [List.reverse_append, List.reverse_cons]
  rw [← hab, List.reverse_reverse] at key
  refine ⟨b.reverse ++ [x], a.reverse, key, ?_, by simp⟩
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_append_of_ne_nil _ (by simp)]
  simp

/-- **HOL `last_flatten`**（tame_list.hl:11922，批 37 同证重定型
`List (List (ℕ × ℕ))` 面）`~(r = []) /\ all nonnil r ==>
LAST (flatten r) = LAST (LAST r)`。 -/
private theorem lastFlattenPair {t : List (List (ℕ × ℕ))} (hne : t ≠ [])
    (hall : ∀ p ∈ t, p ≠ []) : t.flatten.getLast! = t.getLast!.getLast! := by
  have hmem : t.getLast! ∈ t := getLastMem' hne
  have hlastNE : t.getLast! ≠ [] := hall _ hmem
  have hflat : t.flatten ≠ [] := by
    intro hc
    exact hlastNE ((flattenEqNilPair t).mp hc _ hmem)
  have hlastGNE : t.getLast hne ≠ [] := by
    rw [← getLast!EqGetLast' hne]
    exact hlastNE
  rw [getLast!EqGetLast' hflat, getLast!EqGetLast' hne,
    List.getLast_flatten_eq_getLast_getLast hflat hlastGNE,
    getLast!EqGetLast' hlastGNE]

/-! ### §3 主件：parts_characterize（tame_list.hl:11946-:12106） -/

/-- **HOL `parts_characterize`**（tame_list.hl:11946-:12106）
`~(r=[]) /\ uniq r /\ flatten prt = r /\ all (\p. ~(p=[])) prt /\
(!p d. MEM p prt /\ MEM d p /\ ~(d = LAST r) ==>
  (~(next_el r d = f_list L (e_list d)) <=> d = LAST p)) ==>
parts L r = prt`——sizeInduct 归纳主体：闭分支 partsPure + prt 逐层
拆（双层 cons 支经 memImpNotUniqCat 爆 uniq）；裂分支 catFrom 把 prt
在含 LAST u 的件 p 处二分，主假设 (p, LAST u) 槽 + 裂支假设换出
LAST u = LAST p，lastFlattenPair + eqseqCat3 收 flatten 半边，IH 双发
+ partsCat 收口。 -/
theorem partsCharacterize (L : fgraph ℕ) {r : List (ℕ × ℕ)}
    {prt : List (List (ℕ × ℕ))} (hne : r ≠ []) (hun : r.Nodup)
    (hfl : prt.flatten = r) (hall : ∀ p ∈ prt, p ≠ [])
    (hH : ∀ p ∈ prt, ∀ d ∈ p, d ≠ r.getLast! →
      (nextEl r d ≠ fList L (eList d) ↔ d = p.getLast!)) :
    partsSpine L r = prt := by
  refine sizeInduct
    (P := fun w => ∀ q, w ≠ [] → w.Nodup → q.flatten = w →
      (∀ j ∈ q, j ≠ []) →
      (∀ j ∈ q, ∀ d ∈ j, d ≠ w.getLast! →
        (nextEl w d ≠ fList L (eList d) ↔ d = j.getLast!)) →
      partsSpine L w = q)
    ?_ r prt hne hun hfl hall hH
  intro i IH w hw q hne' hun' hfl' hall' hH'
  rcases partsCases (fun d => fList L (eList d)) w with hc |
    ⟨u, v, x, hruv, hx, hu, hv, hne2⟩
  · -- 闭分支：parts L w = [w]，prt 逐层拆
    rw [partsPure L hne' hun' hc]
    cases q with
    | nil =>
      exfalso
      rw [List.flatten_nil] at hfl'
      exact hne' hfl'.symm
    | cons h t =>
      cases t with
      | nil =>
        -- flatten [h] = h ++ [] = w ⇒ h = w
        have hhh : h = w := by
          rw [List.flatten_cons, List.flatten_nil, List.append_nil] at hfl'
          exact hfl'
        rw [hhh]
      | cons h' t' =>
        exfalso
        have hh : h ≠ [] := hall' h List.mem_cons_self
        have hh' : h' ≠ [] := hall' h' (List.mem_cons_of_mem _ List.mem_cons_self)
        have hmemh : h.getLast! ∈ h := getLastMem' hh
        have hrr : w = h ++ (h' ++ t'.flatten) := by
          rw [← hfl']
          simp only [List.flatten_cons]
        have hmemr : h.getLast! ∈ w := by
          rw [hrr]
          exact List.mem_append.mpr (Or.inl hmemh)
        -- LAST h ≠ LAST w：否则 LAST h 同居于两半，memImpNotUniqCat 爆 uniq
        have hnelast : h.getLast! ≠ w.getLast! := by
          intro hEq
          have hrest : h' ++ t'.flatten ≠ [] :=
            List.append_ne_nil_of_left_ne_nil hh' _
          have hmem2 : h.getLast! ∈ h' ++ t'.flatten := by
            rw [hEq, hrr, Kepler.Graphs.getLast!_append_of_ne_nil hrest]
            exact getLastMem' hrest
          have hund : (h ++ (h' ++ t'.flatten)).Nodup := by
            rw [← hrr]; exact hun'
          exact memImpNotUniqCat hmemh hmem2 hund
        -- 闭分支在 d = LAST h 槽给 next_el w (LAST h) = f_list；
        -- 主假设同槽（右半恒真）给 ≠，相抵
        rcases hc h.getLast! hmemr with h0 | h0
        · exact hnelast h0
        · exact absurd h0
            ((hH' h List.mem_cons_self h.getLast! hmemh hnelast).mpr rfl)
  · -- 裂分支：w = u ++ v，x = LAST u，next_el w x ≠ f_list (e_list x)
    have hilm := partsInductLemma hun' hruv hu hv
    have hund2 : (u ++ v).Nodup := by rw [← hruv]; exact hun'
    have hxu : x ∈ u := by rw [← hx]; exact getLastMem' hu
    have hxr : x ∈ w := by
      rw [hruv]
      exact List.mem_append.mpr (Or.inl hxu)
    have hxrfl : x ∈ q.flatten := by rw [hfl']; exact hxr
    obtain ⟨p, hpq, hxp⟩ := List.mem_flatten.mp hxrfl
    -- catFrom：prt = pre ++ post，LAST pre = p（件级二分位置）
    obtain ⟨pre, post, hpqr, hpreLast, hpreNe⟩ := catFromPair hpq
    -- x ≠ LAST w：x ∈ u，若 x = LAST v 则跨居两半爆 uniq（r = (u++v)）
    have hxvne : x ≠ v.getLast! := by
      intro hc0
      exact ((List.nodup_append.mp hund2).2.2 x hxu x
        (by rw [hc0]; exact getLastMem' hv)) rfl
    have hxneLast : x ≠ w.getLast! := by
      rw [hruv, Kepler.Graphs.getLast!_append_of_ne_nil hv]
      exact hxvne
    -- 主假设 (p, x) 槽 + 裂支假设 ⇒ x = LAST p
    have hxLastP : x = p.getLast! := (hH' p hpq x hxp hxneLast).mp hne2
    -- pre/post 均承 prt 的成员与全非空
    have hprePrt : ∀ j ∈ pre, j ∈ q := fun j hj => by
      rw [hpqr]; exact List.mem_append.mpr (Or.inl hj)
    have hpostPrt : ∀ j ∈ post, j ∈ q := fun j hj => by
      rw [hpqr]; exact List.mem_append.mpr (Or.inr hj)
    have hpreHall : ∀ j ∈ pre, j ≠ [] := fun j hj => hall' j (hprePrt j hj)
    have hpostHall : ∀ j ∈ post, j ≠ [] := fun j hj => hall' j (hpostPrt j hj)
    have hpPre : p ∈ pre := by rw [← hpreLast]; exact getLastMem' hpreNe
    have hflaNe : pre.flatten ≠ [] := by
      intro hc0
      exact hpreHall p hpPre ((flattenEqNilPair pre).mp hc0 p hpPre)
    -- LAST (flatten pre) = LAST u（lastFlattenPair + x = LAST p）
    have hlastU : pre.flatten.getLast! = u.getLast! := by
      rw [lastFlattenPair hpreNe hpreHall, hpreLast, ← hxLastP, ← hx]
    have hflatPrePost : pre.flatten ++ post.flatten = w := by
      rw [← List.flatten_append, ← hpqr, hfl']
    have hunflat : (pre.flatten ++ post.flatten).Nodup := by
      rw [hflatPrePost]; exact hun'
    -- eqseq_cat3 收长度半边：flatten pre = u /\ flatten post = v
    have hsplit := eqseqCat3 hflaNe hu hlastU hunflat
      (hflatPrePost.trans hruv)
    -- 逐件假设换面：next_el w ↦ next_el u（next_el_cat1）
    have hHpre : ∀ j ∈ pre, ∀ d ∈ j, d ≠ u.getLast! →
        (nextEl u d ≠ fList L (eList d) ↔ d = j.getLast!) := by
      intro j hj d hd hdne
      have hdU : d ∈ u := by
        have hdm : d ∈ pre.flatten := List.mem_flatten.mpr ⟨j, hj, hd⟩
        rw [← hsplit.1]; exact hdm
      have hdne2 : d ≠ w.getLast! := by
        intro hc0
        rw [hruv, Kepler.Graphs.getLast!_append_of_ne_nil hv] at hc0
        exact ((List.nodup_append.mp hund2).2.2 d hdU d
          (by rw [hc0]; exact getLastMem' hv)) rfl
      have hkey := hH' j (hprePrt j hj) d hd hdne2
      have hnext : nextEl w d = nextEl u d := by
        rw [hruv]
        exact nextElCat1 hilm.2.2.1 hdU hdne
      rw [hnext] at hkey
      exact hkey
    -- 逐件假设换面：next_el w ↦ next_el v（next_el_cat2）
    have hHpost : ∀ j ∈ post, ∀ d ∈ j, d ≠ v.getLast! →
        (nextEl v d ≠ fList L (eList d) ↔ d = j.getLast!) := by
      intro j hj d hd hdne
      have hdV : d ∈ v := by
        have hdm : d ∈ post.flatten := List.mem_flatten.mpr ⟨j, hj, hd⟩
        rw [← hsplit.2]; exact hdm
      have hdne2 : d ≠ w.getLast! := by
        rw [hruv, Kepler.Graphs.getLast!_append_of_ne_nil hv]
        exact hdne
      have hkey := hH' j (hpostPrt j hj) d hd hdne2
      have hnext : nextEl w d = nextEl v d := by
        rw [hruv]
        exact nextElCat2 hund2 hdV hdne
      rw [hnext] at hkey
      exact hkey
    -- 收口：parts w = parts u ++ parts v = pre ++ post = prt
    rw [partsCat L hruv hx hu hv hne2 hun',
      IH u (by omega) pre hu hilm.2.2.1 hsplit.1 hpreHall hHpre,
      IH v (by omega) post hv hilm.2.2.2 hsplit.2 hpostHall hHpost]
    exact hpqr.symm

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两件预期零 sorryAx）：
#print axioms Kepler.Text.TameSpine.memImpNotUniqCat
#print axioms Kepler.Text.TameSpine.partsCharacterize
-/
