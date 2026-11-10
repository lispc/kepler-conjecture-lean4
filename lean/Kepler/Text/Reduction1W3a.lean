/-
  Kepler.Text.Reduction1W3a — J4 Wave W3 首波（上）：contour 簇载体 + 桥基件 +
  contour 簇全 7 件（HOL reduction1.hl :3031-:3121 refl/trans、:3251-:3343
  f_list/fe_list/mem/f_list_right/fe_list_right、:3211-:3245 与 :3345-:3357
  桥基）。final_list 连通对（:3122-:3210）在 Reduction1W3b（本波下，同 patch）。

  **载体定案（全簇统一，本文件头记档）**：chain 载体——`Dart := ℕ × ℕ`
  （Reduction5 特化）、`finalList`/`quotientList`（Reduction5Base）、
  `findList`/`oneStepList`/`contourList`/`finalDartList`（ChainListsL1/L2）、
  `listOfDarts`/`fList`/`eList`（Assembly）。理由：下游 `flagList`
  （ChainListsL2）首合取已按此载体落（`contourList L s ∧ {x | x ∈ s} ⊆
  {x | x ∈ finalDartList L N}` 形），本簇结论直喂；HOL 的
  `set_of_list s SUBSET X` 之 `X` 统一落 `Set Dart`（成员谓词载体）。
  HOL 只有一个常量 `contour_list_connected_v2`（`contour_list_connected` 是
  其定义定理的 ML 名，不是第二个常量）——早侦所称 v1/v2 双形不存在。

  三风险点处置：
  · SUBSET/set_of_list 载体：`contourListConnected` 单点定义定载体；
  · `findListUniq` 可见性：TameList9:582 是公开件，零改动消费（经
    ChainBridge `findList_eq_findListSpine` 两形等值桥）；
  · Pwssrat chain 形：`men_f_list_darts`（PWSSRAT.hl:358，无前提）按
    TameLp `dart_in_face`/`mem_darts_of_mem_findFace` 同链在本文件私件重推
    （TameLp `fList_mem_darts` 带 Nodup 证明参，私件免之，陈述与 HOL 逐字）；
    `good_list_e_list` = `GoodList` 第三合取直取（`eList d = (d.2, d.1)`）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.ChainListsL2
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction3DefsAssumptionInst

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts eList fList)
open Kepler.Graphs (fgraph)
open Kepler.Text.ChainLists (findList contourList oneStepList finalDartList)
open Kepler.Text.Reduction5 (Dart quotientList finalList core)

/-! ## §0 私件（getD/getLastD/headD 小工具 + f_list/e_list 成员） -/

/-- cons 表 `headD` 点式方程。 -/
private theorem headDCons (a : Dart) (l : List Dart) :
    (a :: l).headD (0, 0) = a := rfl

/-- 单元表 `getLastD` 点式方程。 -/
private theorem getLastDConsNil (a : Dart) : [a].getLastD (0, 0) = a := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (by simp),
    Option.getD_some]
  rfl

/-- 双 cons 表 `getLastD` 递归方程。 -/
private theorem getLastDConsCons (a b : Dart) (l : List Dart) :
    (a :: b :: l).getLastD (0, 0) = (b :: l).getLastD (0, 0) := by
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
    List.getLast?_cons_cons]

/-- 尾非空的 cons 表 `getLastD` 递归方程。 -/
private theorem getLastDConsNe (a : Dart) {l : List Dart} (hl : l ≠ []) :
    (a :: l).getLastD (0, 0) = l.getLastD (0, 0) := by
  rcases l with _ | ⟨b, l'⟩
  · exact absurd rfl hl
  · exact getLastDConsCons a b l'

/-- append 末位 getLastD（右表非空）。 -/
private theorem getLastDAppend (s : List Dart) {t : List Dart} (hne : t ≠ []) :
    (s ++ t).getLastD (0, 0) = t.getLastD (0, 0) := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, getLastDConsNe x (by simp [hne]), ih]

/-- 非空表 `headD` ∈ 表。 -/
private theorem headDMem {s : List Dart} (h : s ≠ []) : s.headD (0, 0) ∈ s := by
  cases s with
  | nil => exact absurd rfl h
  | cons a l => rw [headDCons]; exact List.mem_cons.mpr (Or.inl rfl)

/-- 非空表 `getLastD` ∈ 表。 -/
private theorem getLastDMem {s : List Dart} (h : s ≠ []) :
    s.getLastD (0, 0) ∈ s := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h, Option.getD_some]
  exact List.getLast_mem h

/-- getD 末下标 = getLastD。 -/
private theorem getDEqLastD : ∀ l : List Dart,
    l.getD (l.length - 1) (0, 0) = l.getLastD (0, 0) := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases l with _ | ⟨x, xs⟩
    · rw [getLastDConsNil]
      rfl
    · rw [show (a :: x :: xs).length - 1 = (x :: xs).length - 1 + 1 by
        rw [List.length_cons, List.length_cons]; omega,
        List.getD_cons_succ, ih, getLastDConsCons]

/-- append 左区 getD（下标在左表内）。 -/
private theorem getDAppendLeft {s t : List Dart} {i : ℕ} (h : i < s.length) :
    (s ++ t).getD i (0, 0) = s.getD i (0, 0) := by
  induction s generalizing i with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
    rcases i with _ | k
    · rw [List.cons_append, List.getD_cons_zero, List.getD_cons_zero]
    · rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
      exact ih (by rw [List.length_cons] at h; omega)

/-- append 右区 getD（无界版本）。 -/
private theorem getDAppendRight (s t : List Dart) (j : ℕ) :
    (s ++ t).getD (s.length + j) (0, 0) = t.getD j (0, 0) := by
  induction s with
  | nil => rw [List.nil_append, List.length_nil, Nat.zero_add]
  | cons x xs ih =>
    rw [List.cons_append, List.length_cons, Nat.add_right_comm xs.length 1 j,
      List.getD_cons_succ, ih]

/-- HOL `men_f_list_darts`（PWSSRAT.hl:358，无前提）：
`MEM d (list_of_darts L) ⇒ MEM (f_list L d) (list_of_darts L)`。 -/
private theorem fListMemDarts {L : fgraph ℕ} {d : Dart} (hd : d ∈ listOfDarts L) :
    fList L d ∈ listOfDarts L :=
  Kepler.Text.TameLp.mem_darts_of_mem_findFace L
    (Kepler.Text.TameLp.nextEl_mem_of_mem
      ((Kepler.Text.TameLp.dart_in_face L d).mpr hd))

/-- HOL `good_list_e_list`（tame_list.hl:3883，前提 = `GoodList`）：
`MEM x (list_of_darts L) ⇒ MEM (e_list x) (list_of_darts L)`——
`GoodList` 第三合取直取（`eList x = (x.2, x.1)` 定义）。 -/
private theorem eListMemDarts {L : fgraph ℕ} (hL : GoodList L) {x : Dart}
    (hx : x ∈ listOfDarts L) : eList x ∈ listOfDarts L :=
  hL.2.2 x hx

/-! ## §1 载体定义：`contour_list_connected_v2`（tame_defs2.hl:715-717） -/

/-- HOL `contour_list_connected_v2`（tame_defs2.hl:715-717）
`?s. ~(s = []) /\ HD s = u /\ LAST s = v /\ contour_list L s /\
set_of_list s SUBSET X`。载体定案见文件头：`HD/LAST` ↦ `headD/getLastD
(0,0)`（junk 缺省同 `flagList` 既落形）、`set_of_list s SUBSET X` ↦
`{x | x ∈ s} ⊆ X`。 -/
def contourListConnected (L : fgraph ℕ) (X : Set Dart) (u v : Dart) : Prop :=
  ∃ s : List Dart, s ≠ [] ∧ s.headD (0, 0) = u ∧ s.getLastD (0, 0) = v ∧
    contourList L s ∧ {x : Dart | x ∈ s} ⊆ X

/-! ## §2 桥基件（reduction1.hl :3211-:3245、:3345-:3357） -/

/-- **HOL `quotient_list_eq_cons`**（reduction1.hl:3211-:3227）
`quotient_list L N = [a;b] ==> ?r1 r2. N = [r1;r2]`——quotient_list_core
（MAP 保长）+ `sizel N = 2` 两元拆分（HOL `size2_cons`）。 -/
theorem quotientListEqCons {L : fgraph ℕ} {N : List (List Dart)} {a b : List ℕ}
    (h : quotientList L N = [a, b]) : ∃ r1 r2 : List Dart, N = [r1, r2] := by
  have hmeq : N.map (core L) = [a, b] :=
    (Kepler.Text.MoreLemma2Island1.quotientListCore L N).symm.trans h
  have h2 : N.length = 2 := by
    have hlen : (N.map (core L)).length = 2 := by rw [hmeq]; rfl
    rwa [List.length_map] at hlen
  rcases N with _ | ⟨r1, _ | ⟨r2, rs⟩⟩
  · exact absurd h2 (by simp)
  · exact absurd h2 (by simp)
  · rcases rs with _ | ⟨x, xs⟩
    · exact ⟨r1, r2, rfl⟩
    · rw [List.length_cons, List.length_cons, List.length_cons] at h2
      omega

/-- **HOL `mem_map_last`**（reduction1.hl:3229-:3245）
`~(xs = []) /\ all (\x. ~(x = [])) xs /\ MEM d (MAP LAST xs) ==> MEM d
(flatten xs)`——MEM_MAP 取证人后 `LAST` 落在该表内（HOL `LAST` 的 junk 值在
Lean 载体为 `getLastD dflt`，前提 `all` 恰挡死 junk 支；`~(xs = [])` 前提
由 `MEM d (MAP LAST xs)` 蕴含，按 HOL 原文保留）。 -/
theorem memMapLast {α : Type*} {dflt : α} {xs : List (List α)} {d : α}
    (hne : xs ≠ []) (halla : ∀ x ∈ xs, x ≠ [])
    (hd : d ∈ xs.map (fun x => x.getLastD dflt)) : d ∈ xs.flatten := by
  obtain ⟨y, hy, hyd⟩ := List.mem_map.mp hd
  have hyne : y ≠ [] := halla y hy
  refine List.mem_flatten.mpr ⟨y, hy, ?_⟩
  rw [← hyd, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hyne,
    Option.getD_some]
  exact List.getLast_mem hyne

/-- **HOL `final_dart_list_final_list`**（reduction1.hl:3345-:3357）
`uniq (flatten N) /\ MEM d (final_dart_list L N) ==> final_list L
(find_list N d)`——flatten/filter 拆条 + find_list_uniq（TameList9:582
公开件，经 ChainBridge 两形等值桥）收口。 -/
theorem finalDartListFinalList {L : fgraph ℕ} {N : List (List Dart)} {d : Dart}
    (hun : N.flatten.Nodup) (hd : d ∈ finalDartList L N) :
    finalList L (findList N d) := by
  unfold finalDartList at hd
  obtain ⟨r, hr, hdr⟩ := List.mem_flatten.mp hd
  obtain ⟨hrN, hdec⟩ := List.mem_filter.mp hr
  have hfin : finalList L r := of_decide_eq_true hdec
  have hfeq : findList N d = r := by
    rw [Kepler.Text.ChainBridge.findList_eq_findListSpine]
    exact Kepler.Text.TameSpine.findListUniq hun hdr hrN
  rw [hfeq]
  exact hfin

/-! ## §3 contour：refl / mem / 两元证人 / f_list / fe_list
（reduction1.hl :3031-:3048、:3299-:3313、:3251-:3298） -/

/-- **HOL `contour_list_connected_refl`**（reduction1.hl:3031-:3048）：
`u IN X /\ MEM u (list_of_darts L) ==> contour_list_connected_v2 L X u u`
——证人 `[u]`。 -/
theorem contourListConnectedRefl {L : fgraph ℕ} {X : Set Dart} {u : Dart}
    (huX : u ∈ X) (huD : u ∈ listOfDarts L) :
    contourListConnected L X u u := by
  refine ⟨[u], List.cons_ne_nil _ _, headDCons u [], getLastDConsNil u, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with hx1 | hx1
      · rw [hx1]; exact huD
      · exact absurd hx1 (List.not_mem_nil)
    · intro i hi
      rw [List.length_cons, List.length_nil] at hi
      omega
  · intro x hx
    rcases List.mem_cons.mp hx with hx1 | hx1
    · rw [hx1]; exact huX
    · exact absurd hx1 (List.not_mem_nil)

/-- **HOL `contour_list_connected_mem`**（reduction1.hl:3299-:3313）：
`contour_list_connected_v2 L X u v ==> MEM u (list_of_darts L) /\
MEM v (list_of_darts L) /\ u IN X /\ v IN X`——headD/lastD 成员 +
SUBSET 直投。 -/
theorem contourListConnectedMem {L : fgraph ℕ} {X : Set Dart} {u v : Dart}
    (h : contourListConnected L X u v) :
    u ∈ listOfDarts L ∧ v ∈ listOfDarts L ∧ u ∈ X ∧ v ∈ X := by
  obtain ⟨s, hsne, hsH, hsL, hsC, hsSub⟩ := h
  have h1 : u ∈ s := by rw [← hsH]; exact headDMem hsne
  have h2 : v ∈ s := by rw [← hsL]; exact getLastDMem hsne
  exact ⟨hsC.1 u h1, hsC.1 v h2, hsSub h1, hsSub h2⟩

/-- 两元证人 `[a; b]` 的公共装配（Lean 侧提取件，无 HOL 同名：HOL 在
`contour_list_connected_f_list`/`_fe_list` 与 `final_list_connected_lemma`
后段三处各自内联同一个两元证人，此处合一）：两端在 dart 表与 `X` 内、且
`b` 是 `a` 的一步后继（`one_step_list`）⇒ `a` 到 `b` 连通。 -/
theorem contourListConnectedPair {L : fgraph ℕ} {X : Set Dart} {a b : Dart}
    (haD : a ∈ listOfDarts L) (hbD : b ∈ listOfDarts L)
    (haX : a ∈ X) (hbX : b ∈ X) (hstep : oneStepList L a b) :
    contourListConnected L X a b := by
  refine ⟨[a, b], List.cons_ne_nil _ _, headDCons a [b], ?_, ?_, ?_⟩
  · rw [getLastDConsCons, getLastDConsNil]
  · refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with hx1 | hx1
      · rw [hx1]; exact haD
      · rcases List.mem_cons.mp hx1 with hx2 | hx2
        · rw [hx2]; exact hbD
        · exact absurd hx2 (List.not_mem_nil)
    · intro i hi
      rw [List.length_cons, List.length_cons, List.length_nil] at hi
      have hz : i = 0 := by omega
      subst hz
      rw [List.getD_cons_zero, List.getD_cons_succ, List.getD_cons_zero]
      exact hstep
  · intro x hx
    rcases List.mem_cons.mp hx with hx1 | hx1
    · rw [hx1]; exact haX
    · rcases List.mem_cons.mp hx1 with hx2 | hx2
      · rw [hx2]; exact hbX
      · exact absurd hx2 (List.not_mem_nil)

/-- **HOL `contour_list_connected_f_list`**（reduction1.hl:3251-:3274）：
`v IN X /\ f_list L v IN X /\ MEM v (list_of_darts L) ==>
contour_list_connected_v2 L X v (f_list L v)`——证人 `[v; f_list L v]`，
一步邻接 = `one_step_list` 首支 + 私件 `fListMemDarts`。 -/
theorem contourListConnectedFList {L : fgraph ℕ} {X : Set Dart} {v : Dart}
    (hvX : v ∈ X) (hvfX : fList L v ∈ X) (hvD : v ∈ listOfDarts L) :
    contourListConnected L X v (fList L v) :=
  contourListConnectedPair hvD (fListMemDarts hvD) hvX hvfX (Or.inl rfl)

/-- **HOL `contour_list_connected_fe_list`**（reduction1.hl:3275-:3298）：
`good_list L /\ v IN X /\ f_list L (e_list v) IN X /\ MEM v
(list_of_darts L) ==> contour_list_connected_v2 L X v (f_list L (e_list v))`
——证人 `[v; f_list L (e_list v)]`，一步邻接 = `one_step_list` 次支，
`e_list` 成员走 `GoodList` 第三合取。 -/
theorem contourListConnectedFeList {L : fgraph ℕ} (hL : GoodList L) {X : Set Dart}
    {v : Dart} (hvX : v ∈ X) (hvfX : fList L (eList v) ∈ X)
    (hvD : v ∈ listOfDarts L) :
    contourListConnected L X v (fList L (eList v)) :=
  contourListConnectedPair hvD (fListMemDarts (eListMemDarts hL hvD)) hvX hvfX
    (Or.inr rfl)

/-! ## §4 contour：trans / f_list_right / fe_list_right
（reduction1.hl :3049-:3121、:3314-:3343） -/

/-- **HOL `contour_list_connected_trans`**（reduction1.hl:3049-:3121）：
v2 关系沿中点传递——证人 `cat s (TL s')`，head 取 `s` 头；last 分
`TL s' = []`（退化为 `v = w`，回用第一段）与 `TL s' ≠ []`（append 末位 =
`s'` 末位）两支；contour_list 相邻三区（左区 / 接缝 / 右区）。
`hd_cat`↦headDCons、`last_cat`↦getLastDAppend、`Seq.size_cat`↦
`List.length_append`、`EL_APPEND`↦getDAppendLeft/Right、`LAST_EL`↦
getDEqLastD。 -/
theorem contourListConnectedTrans {L : fgraph ℕ} {X : Set Dart} {u v w : Dart}
    (h1 : contourListConnected L X u v) (h2 : contourListConnected L X v w) :
    contourListConnected L X u w := by
  obtain ⟨s, hsne, hsH, hsL, hsC, hsSub⟩ := h1
  obtain ⟨t, htne, htH, htL, htC, htSub⟩ := h2
  rcases t with _ | ⟨b, t'⟩
  · exact absurd rfl htne
  have hb : b = v := by rw [headDCons] at htH; exact htH
  subst hb
  rcases t' with _ | ⟨c, t''⟩
  · -- TL s' = []：s' = [b]，b = w，回用第一段
    rw [getLastDConsNil] at htL
    exact ⟨s, hsne, hsH, hsL.trans htL, hsC, hsSub⟩
  · -- TL s' = c :: t''：证人 s ++ c :: t''
    have hspos : 0 < s.length := List.length_pos_of_ne_nil hsne
    refine ⟨s ++ c :: t'', ?_, ?_, ?_, ?_, ?_⟩
    · intro hc
      exact hsne (List.append_eq_nil_iff.mp hc).1
    · rcases s with _ | ⟨a, l⟩
      · exact absurd rfl hsne
      · rw [List.cons_append, headDCons]
        rw [headDCons] at hsH
        exact hsH
    · rw [getLastDAppend s (List.cons_ne_nil c t''), ← getLastDConsCons b c t'']
      exact htL
    · refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx1
        · exact hsC.1 x hx1
        · exact htC.1 x (List.mem_cons_of_mem _ hx1)
      · intro i hi
        rw [List.length_append] at hi
        rcases Nat.lt_or_ge (i + 1) s.length with hlt1 | hge1
        · -- 左区：两位都在 s 内
          rw [getDAppendLeft (by omega), getDAppendLeft hlt1]
          exact hsC.2 i hlt1
        · rcases Nat.lt_or_ge i s.length with hlt | hge
          · -- 接缝：i = s.length - 1，one_step (LAST s) (HD (TL s'))
            have hieq : i = s.length - 1 := by omega
            subst hieq
            have h01 := htC.2 0 (by
              rw [List.length_cons, List.length_cons]; omega)
            rw [List.getD_cons_zero, List.getD_cons_succ,
              List.getD_cons_zero] at h01
            rw [getDAppendLeft (by omega), getDEqLastD s, hsL,
              show s.length - 1 + 1 = s.length + 0 by omega,
              getDAppendRight s (c :: t'') 0, List.getD_cons_zero]
            exact h01
          · -- 右区：i = s.length + k，两位都在 TL s' 内
            have hr1 := getDAppendRight s (c :: t'') (i - s.length)
            have hr2 := getDAppendRight s (c :: t'') (i - s.length + 1)
            rw [show s.length + (i - s.length) = i by omega] at hr1
            rw [show s.length + (i - s.length + 1) = i + 1 by omega] at hr2
            have hstep := htC.2 (i - s.length + 1) (by
              rw [List.length_cons]; omega)
            rw [List.getD_cons_succ, List.getD_cons_succ] at hstep
            rw [hr1, hr2]
            exact hstep
    · intro x hx
      rcases List.mem_append.mp hx with hx1 | hx1
      · exact hsSub hx1
      · exact htSub (List.mem_cons_of_mem _ hx1)

/-- **HOL `contour_list_connected_f_list_right`**（reduction1.hl:3314-:3327）：
`contour_list_connected_v2 L X u v /\ (f_list L v) IN X ==>
contour_list_connected_v2 L X u (f_list L v)`——trans 取中点 `v`，后段
= `_f_list`，其前提由 `_mem` 供。 -/
theorem contourListConnectedFListRight {L : fgraph ℕ} {X : Set Dart} {u v : Dart}
    (h : contourListConnected L X u v) (hfX : fList L v ∈ X) :
    contourListConnected L X u (fList L v) := by
  obtain ⟨-, hvD, -, hvX⟩ := contourListConnectedMem h
  exact contourListConnectedTrans h (contourListConnectedFList hvX hfX hvD)

/-- **HOL `contour_list_connected_fe_list_right`**（reduction1.hl:3329-:3343）：
`good_list L /\ contour_list_connected_v2 L X u v /\ (f_list L (e_list v))
IN X ==> contour_list_connected_v2 L X u (f_list L (e_list v))`——同上，
后段 = `_fe_list`。 -/
theorem contourListConnectedFeListRight {L : fgraph ℕ} (hL : GoodList L)
    {X : Set Dart} {u v : Dart} (h : contourListConnected L X u v)
    (hfX : fList L (eList v) ∈ X) :
    contourListConnected L X u (fList L (eList v)) := by
  obtain ⟨-, hvD, -, hvX⟩ := contourListConnectedMem h
  exact contourListConnectedTrans h (contourListConnectedFeList hL hvX hfX hvD)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.quotientListEqCons
#print axioms Kepler.Text.Reduction1.memMapLast
#print axioms Kepler.Text.Reduction1.finalDartListFinalList
#print axioms Kepler.Text.Reduction1.contourListConnectedRefl
#print axioms Kepler.Text.Reduction1.contourListConnectedMem
#print axioms Kepler.Text.Reduction1.contourListConnectedPair
#print axioms Kepler.Text.Reduction1.contourListConnectedFList
#print axioms Kepler.Text.Reduction1.contourListConnectedFeList
#print axioms Kepler.Text.Reduction1.contourListConnectedTrans
#print axioms Kepler.Text.Reduction1.contourListConnectedFListRight
#print axioms Kepler.Text.Reduction1.contourListConnectedFeListRight
