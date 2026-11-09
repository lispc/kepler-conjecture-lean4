/-
  Kepler.Text.MoreLemma2QuotientAlt — J 战役 J1（M0h2 第一片）：
  `f_list_quotient_alt` 的 **parts_next_last 半边** + normal_list 合成件。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/tame_list.hl`）──
  │ 本片 2 件公开（+ 私有机器）：
  │   :6408  `parts_next_last`            → partsNextLast
  │   :7180  `normal_list_parts_next_last` → normalListPartsNextLast
  │ 私有机器：
  │   `pia0` 单元素追加分解（parts 的 r = d0 :: rest 分解引擎）
  │   `flattenHead!`（flatten 首元 = 首 atom 首元，all-nonnil 下）
  │   `nextEl_cons_rest`（rest 内元素在 d0::rest 与 rest 的 nextEl 一致）
  │   `loopList_OR`（normalList 合取 4 的 oneStepList 析取形）
  └────────────────────────────────────────────────────────────────

  ┌─ 实现路线（延续 AtomChain 经验：弱不变量直达）─────────────────
  │ `partsNextLast`（x = LAST p 且 x ≠ LAST r ⇒ r 的 next 不等于
  │ f_list∘e_list）：对 r 结构归纳。r = d0 :: rest 时
  │ `parts L r = pia0 (parts L rest) [d0]`（单元素追加分解 + flatten 首元），
  │ 逐步展开 join 条件：stick 支 d0 不可能是 LAST（d0 ∉ rest）；
  │ nonstick 支 p = [d0] 时结论即非 stick 条件、p 为 rest 旧 atom 时收 IH。
  │ 依赖：partsFlatten/partsAllNonnil/partsNonnil（M0e）+ nextEl_eq_getD 族。
  └────────────────────────────────────────────────────────────────

  ┌─ 本片之外（M0h2 第二片，M0h3）────────────────────────────────
  │ `f_list_quotient_alt` 还差 `next_el_parts_last`（:6505）——
  │ 其 HOL 证体经 `next_el_flatten_last`（:5803）; Spine 版实查 ≈90 行
  │ 且带 `nodupOfFlattenNodup`/`nextElCatLast1`/`getD0_append` 等 ~60 行
  │ helper（Spine TameList9:463-540/:1137-1226）⇒ 单独片。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；Dart 具体载体；
  import 闭包零 TameSpine、零 Assembly 主模块。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.ChainListsL1
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2PartsFst

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2QuotientAlt

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart parts partitionIntoAtom partitionIntoAtom0)
open Kepler.Text.ChainLists (normalList fLast loopList)
open Kepler.Text.TameLp (nextEl_eq_getD getD_eq_getElem_of_lt getElem_idxOf idxOf_getElem)
open Kepler.Text.MoreLemma2Island2 (partsFlatten partsAllNonnil partsNonnil)
open Kepler.Text.MoreLemma2Island3 (partsUniqNonnil)
open Kepler.Assembly (fList eList nextEl GoodList)

/-! ## §1 私有机器 -/

/-- `pia0` 单元素追加分解：`pia0 n acc (s ++ [z]) = pia0 n (pia0 n acc s) [z]`。
（parts 的 `r = d0 :: rest` 分解引擎：rev 后单元素尾。） -/
private theorem pia0_append_one {n : Dart → Dart} (z : Dart) :
    ∀ (s : List Dart) (acc : List (List Dart)),
      partitionIntoAtom0 n acc (s ++ [z]) =
        partitionIntoAtom0 n (partitionIntoAtom0 n acc s) [z] := by
  intro s
  induction s with
  | nil => intro acc; rfl
  | cons s0 rest ih =>
    intro acc
    cases acc with
    | nil =>
      rw [List.cons_append]
      simp only [partitionIntoAtom0]
      exact ih [[s0]]
    | cons a0 acc' =>
      rw [List.cons_append]
      simp only [partitionIntoAtom0]
      split_ifs with h
      · exact ih ((s0 :: a0) :: acc')
      · exact ih ([s0] :: a0 :: acc')

/-- flatten 首元 = 首 atom 首元（all-nonnil 下；junk 一致）。 -/
private theorem flattenHead! (L : List (List Dart)) (hn : ∀ a ∈ L, a ≠ []) :
    L.flatten.head! = (L.head!).head! := by
  cases L with
  | nil => rfl
  | cons u t =>
    have hu : u ≠ [] := hn u (List.mem_cons_self ..)
    cases u with
    | nil => exact absurd rfl hu
    | cons a u' =>
      rw [List.flatten_cons]
      rfl

/-- 非空表 `getLast!` 成员。 -/
private theorem getLastMem {l : List Dart} (h : l ≠ []) : l.getLast! ∈ l := by
  have hpos : 0 < l.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- `l[len-1]` 与 `getLast!` 项级换形。 -/
private theorem getElemLastGetLast! {l : List Dart} (hpos : 0 < l.length) :
    l[l.length - 1]'(by omega) = l.getLast! := by
  have h1 : (l[l.length - 1]? : Option Dart).getD default = l[l.length - 1]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, h1]

/-- 下标相等时的 getElem 运输（证明无关）。 -/
private theorem getElemCon {α : Type*} {l : List α} {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (hab : a = b) :
    l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- rest 内元素在 `d0 :: rest` 与 `rest` 上 nextEl 一致（非末元）。 -/
private theorem nextEl_cons_rest {d0 : Dart} {rest : List Dart}
    (hnd : (d0 :: rest).Nodup) {x : Dart} (hx : x ∈ rest)
    (hxl : x ≠ rest.getLast!) : nextEl (d0 :: rest) x = nextEl rest x := by
  have hx0 : x ≠ d0 := by
    intro hc; subst hc; exact (List.nodup_cons.mp hnd).1 hx
  have hpos : 0 < rest.length := List.length_pos_of_mem hx
  have hi : rest.idxOf x < rest.length := List.idxOf_lt_length_iff.mpr hx
  have hi2 : (d0 :: rest).idxOf x = rest.idxOf x + 1 := by
    have hne : d0 ≠ x := fun hc => hx0 hc.symm
    exact List.idxOf_cons_ne rest hne
  have hjl : rest.idxOf x + 1 < rest.length := by
    have hne : rest.idxOf x ≠ rest.length - 1 := by
      intro hc
      refine hxl ?_
      calc x = rest[rest.idxOf x]'(by omega) := (getElem_idxOf hx).symm
        _ = rest[rest.length - 1]'(by omega) := getElemCon _ _ hc
        _ = rest.getLast! := getElemLastGetLast! hpos
    omega
  rw [nextEl_eq_getD (List.mem_cons_of_mem d0 hx), nextEl_eq_getD hx, hi2,
    show rest.idxOf x + 1 + 1 = rest.idxOf x + 2 from by omega,
    List.length_cons,
    Nat.mod_eq_of_lt (show rest.idxOf x + 2 < rest.length + 1 by omega),
    Nat.mod_eq_of_lt hjl,
    getD_eq_getElem_of_lt (show rest.idxOf x + 2 < rest.length + 1 by omega),
    getD_eq_getElem_of_lt hjl]
  rw [List.getElem_cons_succ]

/-- normalList 合取 4 的析取形：`x ∈ r ⟹ nextEl r x = fList x ∨ nextEl r x = fList (eList x)`。 -/
private theorem loopList_OR {L : fgraph ℕ} {r : List Dart}
    (hl : loopList L r) {x : Dart} (hx : x ∈ r) :
    nextEl r x = fList L x ∨ nextEl r x = fList L (eList x) :=
  (hl x hx).2

/-! ## §2 parts_next_last（join 步进状态机；r 结构归纳） -/

/-- **HOL `parts_next_last`**（tame_list.hl:6408
`uniq r ∧ ~(r = []) ==> all (\p. !x. MEM x p ∧ x = LAST p ∧ ~(x = LAST r)
  ==> ~(next_el r x = f_list L (e_list x))) (parts L r)`）。
Spine 现名 `partsNextLast`（TameList9:1318，走 sizeInduct + partsCases 机）。
链岛证体：对 r 结构归纳；`parts L (d0 :: rest) = pia0 (parts L rest) [d0]`
（单元素追加分解）+ join 条件逐步展开；stick 支 d0 不可能是 LAST
（d0 ∉ rest），nonstick 支 p = [d0] 时结论即非 stick 条件、
p 为 rest 旧 atom 时收 IH（`nextEl_cons_rest` 换槽）。 -/
theorem partsNextLast (L : fgraph ℕ) {r : List Dart} :
    r.Nodup → r ≠ [] →
    ∀ p ∈ parts L r, ∀ x ∈ p, x = p.getLast! → x ≠ r.getLast! →
      nextEl r x ≠ fList L (eList x) := by
  intro hun0
  revert hun0
  induction r with
  | nil => intro hun hne; exact absurd rfl hne
  | cons d0 rest ih =>
    intro hun hne p hp x hx hxl hxlast
    cases rest with
    | nil =>
      have hnd : ([d0] : List Dart).Nodup := hun
      have hflat : (parts L [d0]).flatten = [d0] := partsFlatten L hnd (by simp)
      have hxr : x ∈ [d0] := by
        rw [← hflat]
        exact List.mem_flatten.mpr ⟨p, hp, hx⟩
      have hxy : x = d0 := List.mem_singleton.mp hxr
      have hl : ([d0] : List Dart).getLast! = d0 := rfl
      rw [hl] at hxlast
      exact absurd hxy hxlast
    | cons d1 t =>
      have hunRest : (d1 :: t).Nodup := (List.nodup_cons.mp hun).2
      have hneRest : (d1 :: t) ≠ [] := by simp
      have hacc : parts L (d1 :: t) ≠ [] := partsNonnil L hneRest
      have hnlt : ∀ a ∈ parts L (d1 :: t), a ≠ [] :=
        fun a ha => partsAllNonnil L (d1 :: t) a ha
      have hdecomp : parts L (d0 :: d1 :: t)
          = partitionIntoAtom0 (fun d => fList L (eList d)) (parts L (d1 :: t)) [d0] := by
        unfold parts partitionIntoAtom
        rw [show (d0 :: d1 :: t).reverse = (d1 :: t).reverse ++ [d0] from List.reverse_cons ..]
        exact pia0_append_one d0 (n := fun d => fList L (eList d)) (d1 :: t).reverse []
      have hheadA : ((parts L (d1 :: t)).head!).head! = (d1 :: t).head! := by
        conv_lhs => rw [← flattenHead! (parts L (d1 :: t)) hnlt,
          partsFlatten L hunRest hneRest]
      have hny : nextEl (d0 :: d1 :: t) d0 = (d1 :: t).head! := by
        have hi : (d0 :: d1 :: t).idxOf d0 = 0 := List.idxOf_cons_self
        have hm : (0 + 1) % (d0 :: d1 :: t).length = 1 :=
          Nat.mod_eq_of_lt (by simp)
        rw [nextEl_eq_getD (List.mem_cons_self ..), hi, hm,
          getD_eq_getElem_of_lt (by simp)]
        rfl
      have hglr : (d0 :: d1 :: t).getLast! = (d1 :: t).getLast! := rfl
      have hIHpath : ∀ q ∈ parts L (d1 :: t), x ∈ q → x = q.getLast! →
          nextEl (d0 :: d1 :: t) x ≠ fList L (eList x) := by
        intro q hq hxq hxqlast
        have hxr : x ∈ (d1 :: t) := by
          rw [← partsFlatten L hunRest hneRest]
          exact List.mem_flatten.mpr ⟨q, hq, hxq⟩
        have hxl' : x ≠ (d1 :: t).getLast! := by
          intro hc; exact hxlast (by rw [hc]; rfl)
        have hIH := ih hunRest hneRest q hq x hxq hxqlast hxl'
        rwa [nextEl_cons_rest hun hxr hxl']
      obtain ⟨a0, acc', hAcases⟩ : ∃ a0 acc', parts L (d1 :: t) = a0 :: acc' := by
        cases hh : parts L (d1 :: t) with
        | nil => exact absurd hh hacc
        | cons a0 acc' => exact ⟨a0, acc', rfl⟩
      have ha0mem : a0 ∈ parts L (d1 :: t) := by
        rw [hAcases]; exact List.mem_cons_self ..
      have ha0ne : a0 ≠ [] := partsAllNonnil L (d1 :: t) a0 ha0mem
      rw [hdecomp, hAcases] at hp
      simp only [partitionIntoAtom0] at hp
      by_cases hcond : fList L (eList d0) == a0.headD d0
      · rw [if_pos hcond] at hp
        rcases List.mem_cons.mp hp with hp' | hp'
        · rw [hp'] at hx hxl
          have hgl : (d0 :: a0).getLast! = a0.getLast! := by
            cases a0 with
            | nil => exact absurd rfl ha0ne
            | cons _ _ => rfl
          rw [hgl] at hxl
          rcases List.mem_cons.mp hx with hx2 | hx2
          · -- x = d0：LAST p ∈ a0 ⊆ rest 与 d0 ∉ rest 矛盾
            rw [hx2] at hxl
            have hxr : d0 ∈ (d1 :: t) := by
              rw [← partsFlatten L hunRest hneRest]
              exact List.mem_flatten.mpr ⟨a0, ha0mem, hxl ▸ getLastMem ha0ne⟩
            exact absurd hxr (List.nodup_cons.mp hun).1
          · exact hIHpath a0 ha0mem hx2 hxl
        · exact hIHpath p (by rw [hAcases]; exact List.mem_cons_of_mem a0 hp') hx hxl
      · rw [if_neg hcond] at hp
        rcases List.mem_cons.mp hp with hp' | hp'
        · rw [hp'] at hx
          have hx2 : x = d0 := by simpa using hx
          subst hx2
          rw [hny]
          intro hcon
          refine hcond (beq_iff_eq.mpr ?_)
          have hhead! : (parts L (d1 :: t)).head! = a0 := by rw [hAcases]; rfl
          rw [← hcon, ← hheadA, hhead!]
          cases a0 with
          | nil => exact absurd rfl ha0ne
          | cons b t' => rfl
        · exact hIHpath p (by rw [hAcases]; exact hp') hx hxl

/-! ## §3 normal_list_parts_next_last（:7180） -/

/-- junk 缺省桥：`getLastD (0,0)` 与 `getLast!` 一致（Dart 的 default = (0,0)）。 -/
private theorem getLastD_zero_eq_getLast! {r : List Dart} :
    r.getLastD (0, 0) = r.getLast! := by
  rw [List.getLastD_eq_getLast?, List.getLast!_eq_getLast?_getD]
  cases r.getLast? with
  | none => rfl
  | some x => rfl

/-- **HOL `normal_list_parts_next_last`**（tame_list.hl:7180
`normal_list L N ∧ MEM r N ∧ MEM p (parts L r) ==>
  next_el r (LAST p) = f_list L (LAST p)`）。
Spine 现名 `normalListPartsNextLast`（TameList10:466）。
链岛证体：`LAST p = LAST r` 支走 normalList 合取 3（fLast）；
否则 loopList 析取 + `partsNextLast` 排除 e_list 支。 -/
theorem normalListPartsNextLast (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N)
    {p : List Dart} (hp : p ∈ parts L r) :
    nextEl r (p.getLast!) = fList L (p.getLast!) := by
  obtain ⟨hun, hne, hpN, hpne, hsub⟩ := partsUniqNonnil L hL hN hr hp
  by_cases hlast : p.getLast! = r.getLast!
  · have hfl' : nextEl r (r.getLast!) = fList L (r.getLast!) := by
      have hf := hN.2.2.1 r hr
      rw [fLast, getLastD_zero_eq_getLast!] at hf
      exact hf
    rw [hlast]
    exact hfl'
  · have hlastP : p.getLast! ∈ p := getLastMem hpne
    have hlastR : p.getLast! ∈ r := hsub _ hlastP
    rcases loopList_OR (hN.2.2.2.1 r hr) hlastR with h1 | h1
    · exact h1
    · exact absurd h1 (partsNextLast L hun hne p hp _ hlastP rfl hlast)

end Kepler.Text.MoreLemma2QuotientAlt

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2QuotientAlt.partsNextLast
#print axioms Kepler.Text.MoreLemma2QuotientAlt.normalListPartsNextLast
