/-
  Kepler.Text.TameSpine.TameList33 — B1 Tame_list 地基批 33：parts 章收口
  （tamespine-port-plan §4 批次表 B1 行；接续批 32 = TameList32.lean，
  批 32 终点 = HOL :11347（good_face_rep 已落；parts_nil/uniq_sing/parts1
  批 31 已收）；本批起点 = HOL :11369 `parts_impure`。行号均按主仓
  reference/flyspeck（commit 1ce0353）实测。

  **章级侦察定论（流程雷先行：章级动工先 grep 全库同名 HOL 锚，本批
  实测零「预记章早已在库」意外，依赖面零缺口、零新载体）**：
  · `parts_impure` :11369-:11412 ↦ 本批新件 `partsImpure`——全库无同名
    前身（grep partsImpure/parts_impure 零命中，非批 31→32 式在库件）；
  · `parts_cat` :6253-:6271 ↦ `partsCat`（TameList9.lean:1030，公开）；
  · `next_el_cat2` :5648-:5655 ↦ `nextElCat2`（TameList9.lean:248，公开）；
  · `parts_pure` :6111-:6122 ↦ `partsPure`（TameList9.lean:817）；
  · `parts_nil` :11348 / `uniq_sing` :11356 / `parts1` :11359 ↦
    `partsNil`/`uniqSing`/`parts1`（批 31，TameList31.lean:168/:175/:183）；
  · `edge_nondeg_f_xor_ni` :4933-:4944 ↦ `edgeNondegFXorNi`
    （TameList8.lean:368，公开）；
  · 批 32 预记 cat1s 槽落实：`Seq.cat1s`（`cat [h] t = h :: t`）无独立
    件，即 `List.cons_append` 定义形——`h :: t = [h] ++ t` 走 rfl/`show`
    换装，零新件（预记照办）。

  **锚行勘误（入档）**：批 32 头注预记「下一未收件 = parts_impure
  :11367」——主仓实测 `let parts_impure` = :11369（:11367-:11368 为
  parts1 收尾 `]);;` + `(* }}} *)` 两行偏移）。

  本批镜像对象（HOL Light Flyspeck，tame_list.hl:11369-:11425）：

  主件：`parts_impure` :11369-:11412
  `!L f. (!x. MEM x f ==> x = LAST f \/ ~(next_el f x =
  f_list L (e_list x))) /\ uniq f ==> parts L f = MAP (\x. [x]) f`
  （证体十八行）——首元破缺表（每 dart 或为 LAST 或 next_el 与 f_list
  不相合）的 parts 全原子化。HOL 逐槽：LIST_INDUCT ↦ List 归纳
  （nil 槽 = partsNil；`t = []` 槽 = parts1）；`parts L (h::t) =
  parts L (cat [h] t)`（Seq.cat1s 换装）+ GMATCH_SIMP_TAC parts_cat ↦
  `partsCat L rfl … hne hun` 直 rw（u = [h]、x = h 分裂点；hne 槽由
  h ∉ t（nodup）+ t ≠ [] ⇒ h ≠ LAST (h::t)（`(h::t).getLast! =
  t.getLast!` junk 折算 + LAST ∈ 表）从前件拉出）；尾墙
  `parts L t = MAP (\x.[x]) t` = 归纳假设直取，t 侧前件重造：
  `x = LAST t` 支经 hlastHT 同链；不相合支经 `next_el_cat2`
  （`nextEl ([h] ++ t) x = nextEl t x`，hnd 槽 = 原件 nodup 定义形
  换装，`x ≠ LAST t` 槽 = 归纳支前提）搬回 h::t 面。

  随收：`final_list_parts` :11413-:11425
  `!L f. good_list L /\ all (\x. MEM x (list_of_darts L)) f /\
  is_edge_nondegenerate (hypermap_of_list L) /\
  final_list L f /\ uniq f ==> parts L f = MAP (\x. [x]) f`
  ——MATCH_MP parts_impure + MESON[edge_nondeg_f_xor_ni] 装配：
  ∀ x ∈ f 槽取不相合支（反证：若相合，与 finalListSpine 的
  `f_list L x = next_el f x` 串接得 `f_list L x = f_list L (e_list x)`，
  与边非退化 `edgeNondegFXorNi` 冲突）；
  `is_edge_nondegenerate (hypermap_of_list L)` 槽沿批 8/10 消费惯例
  `(hypermapOfList L hL).EdgeNondegenerate`。

  终点自然边界：`final_list_parts` 后 = :11428 `dih2k_card_face`
  （dih2k 章开局）。

  依赖面：批链全批 1-32；在库 TameList7（partsSpine/finalListSpine）/
  TameList8（edgeNondegFXorNi）/ TameList9（partsCat/nextElCat2/
  partsPure）/ TameList31（partsNil/parts1）+ Kepler.Assembly
  （nextEl/eList/fList/listOfDarts/GoodList）+ Lean core
  getLast!_cons_eq_getLastD（Init.Data.List.Lemmas:831）/getLastD_cons
  （Basic:355）/getLastD_mem_cons（Lemmas:845）+ Mathlib nodup_cons。
  私件：`getLastMem`（批 9 TameList9.lean:129 同款 private 不跨文件
  可见，批 7→8 惯例同证重推导）。

  诚实记账：本批两件全真证，零新 def、零止损件、零记账债；记批 32
  头注锚行勘误一条（:11367 ↦ 实测 :11369，见上）。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 34 接续点：HOL :11428 `dih2k_card_face`
  `!k H x. ~(k=0) /\ dih2k H k /\ x IN (dart H) ==>
  CARD (face H x) = k`
  （开局侦察预记：`dih2k` 五合取 ↦ `Kepler.Text.dih2k_p3`（批 29/30
  载体，WRGCVDR.hl:86 主仓实测桩位；批 30 头注档）；HOL 证体两前置槽
  `node_map_and_darts`（hypermap.hl:114）↦ 批 29 载体面
  （TameList29.lean:37 头注档）；证体核心依赖
  `Lvducxu.DIH2K_FACE_SIMPLIZED` 全库未见（grep 零命中）——Lvducxu
  模块面系批 34 真缺口，章级侦察后定槽；`simple_hypermap` 槽 ↦
  `Hypermap.Simple`（批 32 惯例）。）
-/

import Kepler.Text.TameSpine.TameList32

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList fList listOfDarts GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList)

/-! ### §0 LAST-成员私件（批 9 同款重推导） -/

/-- 非空表 `getLast!` 成员（junk 吸收后的 LAST-成员载体件；批 9 私件
`getLastMem`（TameList9.lean:129）同证重推导，private 不跨文件可见）。 -/
private theorem getLastMem {l : List (ℕ × ℕ)} (h : l ≠ []) : l.getLast! ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    rw [List.getLast!_cons_eq_getLastD]
    exact List.getLastD_mem_cons

/-! ### 主件 parts_impure（tame_list.hl:11369-:11412） + 同章收口件 -/

/-- **HOL `parts_impure`**（tame_list.hl:11369-:11412）
`!L f. (!x. MEM x f ==> x = LAST f \/ ~(next_el f x =
f_list L (e_list x))) /\ uniq f ==> parts L f = MAP (\x. [x]) f`
——首元破缺表的 parts 全原子化（HOL LIST_INDUCT + parts_cat 分裂 +
next_el_cat2 搬迁，逐槽见头注）。 -/
theorem partsImpure (L : fgraph ℕ) (f : List (ℕ × ℕ))
    (hp : ∀ x ∈ f, x = f.getLast! ∨ nextEl f x ≠ fList L (eList x))
    (hun : f.Nodup) :
    partsSpine L f = f.map (fun x => [x]) := by
  revert hun
  revert hp
  induction f with
  | nil =>
    intro _ _
    rw [partsNil L]
    rfl
  | cons h t ih =>
    intro hp hun
    obtain ⟨hout, hunT⟩ := List.nodup_cons.mp hun
    by_cases ht0 : t = []
    · -- t = [] 槽（HOL ASM_REWRITE_TAC[MAP;parts1]）：parts1 直取
      subst ht0
      rw [parts1 L h]
      rfl
    · -- junk 折算：LAST (h::t) = LAST t（core getLast!_cons_eq_getLastD 链）
      have hlastHT : (h :: t).getLast! = t.getLast! := by
        rw [List.getLast!_cons_eq_getLastD]
        cases t with
        | nil => exact absurd rfl ht0
        | cons b u =>
          rw [List.getLast!_cons_eq_getLastD]
          exact List.getLastD_cons
      -- 分裂点 x = h 的不相合槽（HOL FIRST_X_ASSUM_ST `LAST` + MESON）：
      -- h = LAST (h::t) = LAST t ∈ t 与 h ∉ t（nodup）矛盾
      have hh : nextEl (h :: t) h ≠ fList L (eList h) := by
        rcases hp h (List.mem_cons_self ..) with h1 | h1
        · refine absurd ?_ hout
          rw [h1, hlastHT]
          exact getLastMem ht0
        · exact h1
      -- t 侧前件重造（HOL ASM_SIMP_TAC + next_el_cat2 搬迁）
      have hpT : ∀ x ∈ t, x = t.getLast! ∨ nextEl t x ≠ fList L (eList x) := by
        intro x hx
        rcases hp x (List.mem_cons_of_mem _ hx) with h1 | h1
        · exact Or.inl (h1.trans hlastHT)
        · by_cases hx2 : x = t.getLast!
          · exact Or.inl hx2
          · refine Or.inr fun hc => h1 ?_
            have hnext : nextEl (h :: t) x = nextEl t x := by
              show nextEl ([h] ++ t) x = nextEl t x
              exact nextElCat2 hun hx hx2
            rw [hnext]
            exact hc
      -- parts_cat 分裂（HOL Seq.cat1s 换装 + GMATCH_SIMP_TAC parts_cat）
      -- + 尾墙归纳假设直取（HOL CONCLUSION）
      rw [partsCat L (r := h :: t) (u := [h]) (v := t) (x := h) rfl
        (by simp) (List.cons_ne_nil h []) ht0 hh hun,
        parts1 L h, ih hpT hunT]
      rfl

/-- **HOL `final_list_parts`**（tame_list.hl:11413-:11425）
`!L f. good_list L /\ all (\x. MEM x (list_of_darts L)) f /\
is_edge_nondegenerate (hypermap_of_list L) /\
final_list L f /\ uniq f ==> parts L f = MAP (\x. [x]) f`
——MATCH_MP parts_impure 装配：∀ x ∈ f 槽的不相合支 = finalListSpine
（`f_list L x = next_el f x`）与 `edge_nondeg_f_xor_ni` 的 MESON 冲突
链（若相合则 `f_list L x = f_list L (e_list x)`，与边非退化矛盾）。 -/
theorem finalListParts (L : fgraph ℕ) (hL : GoodList L) (f : List (ℕ × ℕ))
    (hD : ∀ x ∈ f, x ∈ listOfDarts L)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hf : finalListSpine L f) (hun : f.Nodup) :
    partsSpine L f = f.map (fun x => [x]) := by
  refine partsImpure L f ?_ hun
  intro x hx
  refine Or.inr fun hc => edgeNondegFXorNi hL hnedg (hD x hx) ?_
  exact (hf x hx).trans hc

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；两主件预期标准三
[propext, Classical.choice, Quot.sound]）：
#print axioms Kepler.Text.TameSpine.partsImpure
#print axioms Kepler.Text.TameSpine.finalListParts
-/
