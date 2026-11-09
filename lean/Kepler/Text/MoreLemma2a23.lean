/-
  Kepler.Text.MoreLemma2a23 — J 战役 J1（M0a 收尾片）：pplhulj/qcdvkea/pnxvwfs
  三文件 16 定理中**不依赖 `transform_assumption_v2` 槽**的全部件。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/pplhulj.hl`）──
  │ 本片 3 件公开 + 1 件机器：
  │   pplhulj.hl:33  `marked_list_of_dart`   → markedListOfDart
  │   pplhulj.hl:48  `ytran_me_f`            → ytranMeF
  │   pplhulj.hl:97  `mem_next_mark_inface`  → memNextMarkInface
  │   机器：PWSSRAT.hl:376 `mem_f_list_power`（`(f_list L POWER k) d`
  │         成员留在 `find_face L d`）→ memFListPower（ytran_me_f 的幂链引擎；
  │         Spine 版 TameList12 同名前缀）
  │ `indexl_hd`(:78) 与 `min_num_le`(qcdvkea.hl:32) 已在 M0a 首片落库
  │ （indexlHd / minNumLE，MoreLemma2Aux.lean）。
  └────────────────────────────────────────────────────────────────

  ┌─ 勘误（机器证据推翻工单「载体全就位，13 件可做」）──────────────
  │ 三文件 16 定理逐条核对 HOL 原文：**10 件的陈述本身以
  │ `transform_assumption_v2 L` 为前提**（pnxvwfs 5/5、qcdvkea 2/2、
  │ pplhulj 3/7：ztran_me_f / indexf_ytrans_eq_l_m / PPLHULJ3 / PPLHULJ
  │ —— 计 4 件，另加 ztran_me_f 内嵌）= 该槽是 tame_defs2.hl:568-571 的
  │ 2 行 **new_definition'**（`!N r x. good_list L ∧ good_list_nodes L ∧
  │ marked_list L N r x ==> marked_list L (ntrans…) (rtrans…) x`），
  │ 但链世界**未定义**（Reduction3Thm2.lean:89 头注「缺口 A」；
  │ T2 commit 9e3cbc26 亦以「AQ 批E落库后一行代入」记档）——属 **J2 领土**，
  │ 按 DEF-FIX 纪律本片不越权立槽。
  │ 另即使立槽，其证明体也硬挂**未移植的命名章层**：Pbflhet 7 件
  │ （lt_indexf_in_rtrans_suc_not_rtrans / indexf_const_le_indexf_ytrans /
  │ ztrans_in_suc / ztran_suc_in_rtrans / ztrans_suc_in_ztran_w /
  │ w_betwn_ztrans_ytran0 / PBFLHET + FINAL_LIST_INDUCT1）、Ncvibwu 2 件、
  │ OHCGKFU、Pwssrat.f_list_power_next_el/next_el_sizel、
  │ ztran_in_face_ytrans（全树零命中）、Tame_list.HQYMRTX1_list、
  │ AQIUNPP3（M0f #37，同挂 J2）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体 ────────────────────────────────────────────────────────
  │ `marked_list` = `ChainLists.markedList L hL N r x`（L2 e3a56b3b，
  │   9 合取；合取 2 = normalList、3 = r ∈ N、4 = x ∈ r、6 = next_el r x = f_list L x）；
  │ `ytrans` = `Reduction5.ytrans L N r x i = ly L (rtrans …) x =
  │   (fList L)^[succ (lm …)] x`（Reduction5Base:186 + ytrans_def rfl）；
  │ `find_face`/`f_list` = `findFaceDarts`/`fList`（GoodListDefs）；
  │ 链层 findFace 机器：`dart_in_face`（TameLp:5019）、
  │ `mem_darts_of_mem_findFace`(:5039)、`findFaceDarts_congr_of_mem`(:5082)、
  │ `findFace_fList`(:5110)、`nextEl_mem_of_mem`(:4809)。
  │ 零 axiom/sorry/admit/native_decide；import 闭包零 TameSpine/Assembly 主模块。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL2

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.MoreLemma2a23

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart lm ly ytrans rtrans ytrans_def quotientList)
open Kepler.Text.ChainLists (markedList normalList)
open Kepler.Assembly (fList eList listOfDarts findFaceDarts nextEl GoodList)
open Kepler.Text.TameLp (dart_in_face mem_darts_of_mem_findFace
  findFaceDarts_congr_of_mem findFace_fList nextEl_mem_of_mem)

/-! ## §1 marked_list 成员件（HOL `marked_list_of_dart`，pplhulj.hl:33）

HOL 证体：marked_list 展开 → normal_list 的 loop_list 合取 + `MEM x r`
（marked_list 合取 3/4）直投 `MEM x (list_of_darts L)`。 -/

/-- **HOL `marked_list_of_dart`**（pplhulj.hl:33
`marked_list L N r x ==> MEM x (list_of_darts L)`）。
Spine 无同名（AQ 塔 Spy 链未至）；链岛证体 = markedList 合取 2（normalList）
→ normalList 合取 4（`∀ s ∈ N, loopList L s`）→ loopList 首合取。 -/
theorem markedListOfDart (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hm : markedList L hL N r x) :
    x ∈ listOfDarts L :=
  ((hm.2.1.2.2.2.1 r hm.2.2.1) x hm.2.2.2.1).1

/-! ## §2 f_list 幂成员机器（PWSSRAT.hl:376 `mem_f_list_power`）

`(f_list L POWER k) d` 留在 `find_face L d` 内（d 是 dart 时）。
链岛证体：`findFaceDarts_congr_of_mem`（同面 dart 同 face）+
`findFace_fList`（f_list 保面）+ `nextEl_mem_of_mem`，对 k 归纳。
注：HOL `uniq (list_of_darts L)` 前提经 `GoodList.1` 供给（本件取显式
Nodup 参数以复用）。 -/

/-- **HOL `mem_f_list_power`**（PWSSRAT.hl:376
`!k. uniq (list_of_darts L) /\ MEM d (list_of_darts L) ==>
  MEM (((f_list L) POWER k) d) (find_face L d)`）。
以 `d ∈ find_face L d` 为等价前提形（`dart_in_face` 双向桥）。 -/
theorem memFListPower (L : fgraph ℕ) (hn : (listOfDarts L).Nodup) {d : Dart}
    (hd : d ∈ findFaceDarts L d) : ∀ k : ℕ, (fList L)^[k] d ∈ findFaceDarts L d := by
  intro k
  induction k with
  | zero => simpa using hd
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hz : (fList L)^[k] d ∈ findFaceDarts L d := ih
    have hzd : (fList L)^[k] d ∈ listOfDarts L :=
      mem_darts_of_mem_findFace L hz
    have hcong : findFaceDarts L ((fList L)^[k] d) = findFaceDarts L d :=
      findFaceDarts_congr_of_mem hn (mem_darts_of_mem_findFace L hd) hz
    have hzz : (fList L)^[k] d ∈ findFaceDarts L ((fList L)^[k] d) := by
      rw [hcong]; exact hz
    have hstep : fList L ((fList L)^[k] d) ∈ findFaceDarts L ((fList L)^[k] d) :=
      nextEl_mem_of_mem hzz
    rwa [hcong] at hstep

/-! ## §3 pplhulj 纯 marked_list 件（2 件，无 transform_assumption_v2） -/

/-- **HOL `ytran_me_f`**（pplhulj.hl:48
`good_list L /\ marked_list L N r x /\ f = find_face L x ==>
  MEM (ytrans L N r x i) f`）。
Spine 无同名；HOL 证体 `mem_f_list_power` + `marked_list_of_dart`。
链岛证体：`ytrans … i = ly … = (fList L)^[succ (lm …)] x`（rfl）→
§2 `memFListPower`（x ∈ find_face x 由 markedListOfDart + dart_in_face）。 -/
theorem ytranMeF (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hm : markedList L hL N r x) {f : List Dart}
    (hf : f = findFaceDarts L x) (i : ℕ) : ytrans L N r x i ∈ f := by
  have hx : x ∈ listOfDarts L := markedListOfDart L hL hm
  have hxd : x ∈ findFaceDarts L x := dart_in_face L x |>.mpr hx
  have hpow := memFListPower L hL.1 hxd (Nat.succ (lm L (rtrans L N r x i) x))
  rw [hf, ytrans_def]
  exact hpow

/-- **HOL `mem_next_mark_inface`**（pplhulj.hl:97
`good_list L /\ marked_list L N r x /\ f = find_face L x /\
  w = next_el f x ==> MEM w (find_face L x)`）。
Spine 无同名；HOL 证体 `f_list_power_next_el` + `mem_f_list`。
链岛证体：x ∈ find_face x（markedListOfDart + dart_in_face）λ
`nextEl_mem_of_mem`（w = next_el f x = f_list L x 点态）。 -/
theorem memNextMarkInface (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hm : markedList L hL N r x) {f : List Dart}
    (hf : f = findFaceDarts L x) {w : Dart} (hw : w = nextEl f x) :
    w ∈ findFaceDarts L x := by
  have hx : x ∈ listOfDarts L := markedListOfDart L hL hm
  have hxd : x ∈ findFaceDarts L x := dart_in_face L x |>.mpr hx
  rw [hw, hf]
  exact nextEl_mem_of_mem hxd

/-! ## §4 顺带：M0e 剩件 `quotient_all_uniq`（tame_list.hl:6522）

markedList 合取 5 首项即 `all uniq (quotient_list L N)`（L2 def 逐字对齐
HOL marked_list:1. simple 块）——零成本投影，提前落库以缩短 M0e 欠账。 -/

/-- **HOL `quotient_all_uniq`**（tame_list.hl:6522
`marked_list L N r x ==> all uniq (quotient_list L N)`）。
Spine 现名 `quotientAllUniq`（TameList9:1393）。
链岛证体：markedList 合取 5 的首合取块投影。 -/
theorem quotientAllUniq (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hm : markedList L hL N r x) :
    ∀ q ∈ quotientList L N, q.Nodup :=
  hm.2.2.2.2.1.1

end Kepler.Text.MoreLemma2a23

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.MoreLemma2a23.markedListOfDart
#print axioms Kepler.Text.MoreLemma2a23.memFListPower
#print axioms Kepler.Text.MoreLemma2a23.ytranMeF
#print axioms Kepler.Text.MoreLemma2a23.memNextMarkInface
#print axioms Kepler.Text.MoreLemma2a23.quotientAllUniq
