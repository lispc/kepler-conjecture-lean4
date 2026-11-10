/-
  Kepler.Text.Reduction5J5M2Core — J5-1a 段（chain 载体）：more_lemma2 core 簇
  + 目标件 `next_core_ne_FST`（reduction4.hl:1052）+ 孪生 `ne_fst_imp_f_list`。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ more_lemma2.hl:779 `next_core_FST_SYM`（65L）→ `nextCoreFstSym`：
  │   is_edge_nondegenerate ∧ good_list ∧ good_list_nodes ∧ normal_list L N ∧
  │   r ∈ N ∧ d ∈ r ∧ f_list L d = next_el r d ∧ uniq (core L r)
  │   ⇒ next_el (core L r) (FST d) = FST (next_el r d)
  │ more_lemma2.hl:221 `next_core_FST`（71L）→ `nextCoreFst`（marked 形；
  │   = SYM + marked_list_uniq_core + is_restricted 的边非退化合取，一行推论）；
  │ more_lemma2.hl:39 `FST_next_face_eq_SND` → `fstNextFaceEqSnd`；
  │ reduction4.hl:1052 `next_core_ne_FST`（42L）→ `nextCoreNeFST`（目标件）；
  │ reduction4.hl:5101 `ne_fst_imp_f_list`（38L）→ `neFstImpFList`（孪生）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（比 HOL 短；全走链侧 parts 原子结构）──────────────────────
  │ SYM：d 的原子 p（partsMemExists）、后继的原子 p'（partsMemExists）；
  │  ① `d = p.getLast!`——非 LAST r 支：`conditionLastParts`（原子边界 ⇔
  │    next_el r d ≠ f_list L (e_list d)）+ 假设 f_list L d = next_el r d
  │    ⇒ f_list L d = f_list L (e_list d)，与 `edgeNondegFXorNi`（Island3）
  │    矛盾；LAST r 支：`partsFlatten` + `lastFlatten2` + `uniqSublistUnique`
  │    （HOL 同支，支件 Island2/Island3/Naming 全公开）；
  │  ② `fListQuotientAlt`：f_list L (LAST p) ∈ p' ⇒ next_el (parts L r) p = p'；
  │  ③ `nextElMapApply`（HOL `Tame_list.next_el_MEM_map` 的泛 α 实例：
  │    uniq (map f l) 下 map 后环的 next_el 与原环经 f 对接）；
  │  ④ `partsFst` 两次换回 FST d / FST (next_el r d)。
  │ next_core_ne_FST / ne_fst_imp_f_list：normal_list 的 loop_list 合取
  │  one_step 二分支（f 支 / n⁻¹ 支）——n⁻¹ 支 FST 不变
  │  （`fListFstSnd`（Island3）+ e_list 定义 `(d.2, d.1)`），与 FST u ≠ FST v
  │  矛盾 ⇒ f 支 ⇒ SYM。DIFFERS：HOL 经 loop_list_f_or_ni +
  │  inverse_node_map_list + fst_node_hypermap_of_list + lemma_inverse_in_node
  │  （node 轨道中转）；链侧 one_step 的 n⁻¹ 支已是 f_list L (e_list x)
  │  显式形，免中转。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓双零写入；既有文件零触碰。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL2
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2QuotientAlt2
import Kepler.Text.Reduction4Subseg8
import Kepler.Text.Reduction5TwelveT
import Kepler.Text.TameSpine.TameList59

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList eList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList loopList markedList)

/-! ## §0 泛 α 小引理：map 后环的 next_el 对接 -/

/-- `uniq (l.map f)` 下，`l.map f` 环上的 next_el 与原环经 f 对接
（HOL `Tame_list.next_el_MEM_map` 的泛 α 形，免名依赖）。 -/
private theorem nextElMapApply {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β]
    (f : α → β) {l : List α} (hnd : (l.map f).Nodup) {a : α} (ha : a ∈ l) :
    nextEl (l.map f) (f a) = f (nextEl l a) := by
  have hfa : f a ∈ l.map f := List.mem_map_of_mem ha
  have hilt : l.idxOf a < l.length := List.idxOf_lt_length_iff.mpr ha
  have hmlt : l.idxOf a < (l.map f).length := by rw [List.length_map]; exact hilt
  have hget : (l.map f)[l.idxOf a] = f a := by
    rw [List.getElem_map]
    exact congrArg f (Kepler.Text.TameLp.getElem_idxOf ha)
  have hidx : (l.map f).idxOf (f a) = l.idxOf a := by
    have h := hnd.idxOf_getElem (l.idxOf a) hmlt
    rw [hget] at h
    exact h
  rw [Kepler.Text.TameLp.nextEl_eq_getD hfa, hidx, List.length_map,
    Kepler.Text.TameLp.nextEl_eq_getD ha, List.getD_map]

/-! ## §1 more_lemma2 core 簇 -/

/-- 非空表 `headD (0,0)` = `head!`（McCore 同款重推导）。 -/
private theorem headDHeadBangM2 {l : List Dart} (hne : l ≠ []) :
    l.headD (0, 0) = l.head! := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => rfl

/-- 非空表 `getLast!` = `getLast`。 -/
private theorem getLastBangEqM2 {l : List Dart} (h : l ≠ []) :
    l.getLast! = l.getLast h := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- `getLast` 沿表等式换元。 -/
private theorem getLastCongrM2 {l₁ l₂ : List Dart} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ [])
    (e : l₁ = l₂) : l₁.getLast h₁ = l₂.getLast h₂ := by
  subst e
  rfl

/-- `core L r` 定义级 = parts 经首顶点投影的像。 -/
private theorem coreEqMap (L : fgraph ℕ) (r : List Dart) :
    core L r = (parts L r).map (fun l => (l.headD (0, 0)).1) := rfl

/-- **HOL `More_lemma2.next_core_FST_SYM`**（more_lemma2.hl:779）。 -/
theorem nextCoreFstSym (L : fgraph ℕ) (hL : GoodList L)
    (hen : (hypermapOfList L hL).EdgeNondegenerate)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    {d : Dart} (hd : d ∈ r) (hfd : fList L d = nextEl r d)
    (hcu : (core L r).Nodup) :
    nextEl (core L r) d.1 = (nextEl r d).1 := by
  have hrnd : r.Nodup := (List.nodup_flatten.mp hN.1).1 r hr
  have hrne : r ≠ [] := hN.2.1 r hr
  have hloop : loopList L r := hN.2.2.2.1 r hr
  have hdD : d ∈ listOfDarts L := (hloop d hd).1
  obtain ⟨p, hp, hdp⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hd
  have hnr : nextEl r d ∈ r := Kepler.Text.TameLp.nextEl_mem_of_mem hd
  obtain ⟨p', hp', hnp'⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hnr
  have hpne : p ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r p hp
  have hp'ne : p' ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r p' hp'
  have hfst : d.1 = (p.headD (0, 0)).1 := by
    rw [headDHeadBangM2 hpne]
    exact Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hr hp hdp
  have hfst' : (nextEl r d).1 = (p'.headD (0, 0)).1 := by
    rw [headDHeadBangM2 hp'ne]
    exact Kepler.Text.MoreLemma2PartsFst.partsFst L hL hN hr hp' hnp'
  -- ① d = p.getLast!
  have hdlast : d = p.getLast! := by
    by_cases hdl : d = r.getLast!
    · -- LAST r 支：r = flatten (parts L r)，末原子的末元
      have hpf : (parts L r).flatten = r :=
        Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne
      have hpsne : parts L r ≠ [] := Kepler.Text.MoreLemma2Naming.memImpNotNil hp
      have hlastmem : (parts L r).getLast hpsne ∈ parts L r := List.getLast_mem hpsne
      have hlastne : (parts L r).getLast hpsne ≠ [] :=
        Kepler.Text.MoreLemma2Island2.partsAllNonnil L r _ hlastmem
      have hflne : (parts L r).flatten ≠ [] := by rw [hpf]; exact hrne
      have hlf := Kepler.Text.MoreLemma2Naming.lastFlatten2 hpsne hlastne hflne
      have hdL : d = ((parts L r).getLast hpsne).getLast hlastne := by
        rw [← hlf, hdl, getLastBangEqM2 hrne]
        exact getLastCongrM2 hrne hflne hpf.symm
      have hdin : d ∈ (parts L r).getLast hpsne := by
        rw [hdL]; exact List.getLast_mem hlastne
      have hpeq : p = (parts L r).getLast hpsne :=
        Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L r)
          (by rw [hpf]; exact hrnd) p hp _ hlastmem ⟨d, hdp, hdin⟩
      rw [hpeq, getLastBangEqM2 hlastne]
      exact hdL
    · -- 非 LAST r：原子边界刻划 + 边非退化
      by_contra hne'
      have hcond := (conditionLastParts hp hdp hdl hrne hrnd).not.mpr hne'
      have heq : nextEl r d = fList L (eList d) := not_not.mp hcond
      exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL hen hdD (hfd.trans heq)
  -- ② 后继原子
  have hin : fList L (p.getLast!) ∈ p' := by
    rw [← hdlast, hfd]; exact hnp'
  have hnext : nextEl (parts L r) p = p' :=
    (Kepler.Text.MoreLemma2QuotientAlt2.fListQuotientAlt L hL hN hr hr hp hp').mpr hin
  -- ③④ core 环对接
  have hcore := coreEqMap L r
  rw [hfst, hcore, nextElMapApply (f := fun l : List Dart => (l.headD (0, 0)).1) hcu hp,
    hnext, hfst']

/-- **HOL `More_lemma2.next_core_FST`**（more_lemma2.hl:221）：marked 形
（= SYM + `marked_list_uniq_core` + is_restricted 的边非退化合取，一行推论）。 -/
theorem nextCoreFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hf : ¬ finalList L r)
    {d : Dart} (hd : d ∈ r) (hfd : fList L d = nextEl r d) :
    nextEl (core L r) d.1 = (nextEl r d).1 :=
  nextCoreFstSym L hL hm.1.edgeNondegenerate hgn hm.2.1 hm.2.2.1 hd hfd
    (Kepler.Text.Reduction4Idx.markedListUniqCore L hL hm)

/-- **HOL `More_lemma2.FST_next_face_eq_SND`**（more_lemma2.hl:39）：
`FST (next_el (find_face L x) x) = SND x`（f_list 定义即 next_el (find_face)）。 -/
theorem fstNextFaceEqSnd (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hf : ¬ finalList L r) :
    (nextEl (findFaceDarts L x) x).1 = x.2 := by
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  exact Kepler.Text.MoreLemma2Island3.fListFstSnd L hunL hx

/-! ## §3 reduction4：`next_core_ne_FST` / `ne_fst_imp_f_list` -/

/-- loop_list 的 one_step 二分支在首顶点相异时只剩 f 支
（n⁻¹ 支 `f_list L (e_list u)` 的 FST = FST u）。 -/
private theorem fListEqNextOfNeFst (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    {u v : Dart} (hu : u ∈ r) (hne : u.1 ≠ v.1) (hnext : nextEl r u = v) :
    fList L u = nextEl r u := by
  have hloop : loopList L r := hN.2.2.2.1 r hr
  obtain ⟨huD, hstep⟩ := hloop u hu
  rcases hstep with h | h
  · exact h.symm
  · exfalso
    have hunL : ∀ l ∈ L, l.Nodup :=
      Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
    have heD : eList u ∈ listOfDarts L := hL.2.2 u huD
    have hfs : (fList L (eList u)).1 = (eList u).2 :=
      Kepler.Text.MoreLemma2Island3.fListFstSnd L hunL heD
    have hv1 : v.1 = u.1 := by
      rw [← hnext, h, hfs]
      rfl
    exact hne hv1.symm

/-- **HOL `next_core_ne_FST`**（reduction4.hl:1052）：
`good_list ∧ good_list_nodes ∧ is_restricted ∧ normal_list L N ∧ r ∈ N ∧ u ∈ r ∧
uniq (core L r) ∧ FST u ≠ FST v ∧ next_el r u = v ⇒
next_el (core L r) (FST u) = FST v`。 -/
theorem nextCoreNeFST (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    {u v : Dart} (hu : u ∈ r) (hcu : (core L r).Nodup)
    (hne : u.1 ≠ v.1) (hnext : nextEl r u = v) :
    nextEl (core L r) u.1 = v.1 := by
  have hfu := fListEqNextOfNeFst L hL hgn hres hN hr hu hne hnext
  rw [← hnext]
  exact nextCoreFstSym L hL hres.edgeNondegenerate hgn hN hr hu hfu hcu

/-- **HOL `ne_fst_imp_f_list`**（reduction4.hl:5101）：同前件 ⇒ `f_list L u = v`。 -/
theorem neFstImpFList (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    {u v : Dart} (hu : u ∈ r) (hcu : (core L r).Nodup)
    (hne : u.1 ≠ v.1) (hnext : nextEl r u = v) :
    fList L u = v := by
  rw [fListEqNextOfNeFst L hL hgn hres hN hr hu hne hnext, hnext]

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.nextCoreFstSym
#print axioms Kepler.Text.Reduction5.nextCoreFst
#print axioms Kepler.Text.Reduction5.fstNextFaceEqSnd
#print axioms Kepler.Text.Reduction5.nextCoreNeFST
#print axioms Kepler.Text.Reduction5.neFstImpFList
