/-
  Kepler.Text.Reduction1Mee — J4 W4 后波（下）：MEEIXJO 叶件（HOL MEEIXJO.hl
  九件辅助件，:18-:323 共 307 行）之 Lean 移植。

  本文件九件（按 HOL 原序）：
  · `eListLast`（HOL `e_list_last` :18-:52，36 行）
  · `markedFinalListEx`（HOL `marked_final_list_ex` :54-:61，9 行）
  · `isoListFinalDartList`（HOL `iso_list_final_dart_list` :63-:88，27 行）
  · `injOnContourCondition`（HOL `inj_on_contour_condition` :90-:140，52 行）
  · `injOnContourCondition2`（HOL `inj_on_contour_condition2` :142-:168，29 行）
  · `injOnPower`（HOL `inj_on_power` :171-:195，26 行）
  · `injOnNormalList`（HOL `inj_on_normal_list` :197-:213，18 行）
  · `injOnLM`（HOL `inj_on_l_m` :215-:281，68 行）
  · `injOnSList`（HOL `inj_on_s_list` :283-:323，42 行）
  MEEIXJO 主定理（:325-:604，284 行）**不在本文件**：九合取运输装配留下一波，
  冻结表见 DELIVERY_W4G §3。

  载体沿 Reduction1W3a 文件头定案（chain：`Dart := ℕ × ℕ`、`markedList`/
  `normalList`/`finalList`/`parts`/`listOfDarts`/`fList`/`eList`），Spine 只在
  证体内经 ChainBridge 两形桥出现。折算沿用既有文件头：
  `HD`/`LAST` ↦ `headD (0,0)`/`getLastD (0,0)`（非空守卫下）、
  `set_of_list s SUBSET set_of_list t` ↦ `{x | x ∈ s} ⊆ {x | x ∈ t}`、
  `POWER` ↦ `Function.iterate`、`l'm`/`s_list` ↦ `Reduction5.lm`/
  `ChainLists.sList`。

  **零省前提**：九件前提全部保留、保 HOL 原序（`good_list L` 为载体证人参，
  在 HOL 中本就居首或次位）。`good_list_nodes` 前提在 `inj_on_l_m`/`inj_on_s_list`
  的 HOL 证体内零消费，按原文保留。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W3a
import Kepler.Text.ChainListsL2
import Kepler.Text.ChainBridgeParts
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList2
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList8
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList38
import Kepler.Text.TameSpine.TameList43

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts eList fList nextEl)
open Kepler.Graphs (fgraph)
open Kepler.Text.ChainLists (normalList markedList flagList sFlagList sList
  findList finalDartList)
open Kepler.Text.Reduction5 (Dart quotientList finalList parts lm)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl elementsOfList
  nextEl_mem_of_mem)
open Kepler.Text.TameSpine (NormalListSpine ContourListSpine)

/-! ## §0 私件 -/

/-- 非空表 `getLast!` 必是成员（树内多处私件同证；HOL `MEM_LAST`）。 -/
private theorem getLastMemAux {l : List Dart} (h : l ≠ []) : l.getLast! ∈ l := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h, Option.getD_some]
  exact List.getLast_mem h

/-! ## §1 `e_list_last`（MEEIXJO.hl:18-:52） -/

/-- **HOL `e_list_last`**（MEEIXJO.hl:18-:52）：
`good_list L /\ normal_list L N /\ MEM r N /\ all uniq L /\
is_edge_nondegenerate (hypermap_of_list L) /\ MEM p (parts L r) ==>
MEM (e_list (LAST p)) (flatten N)`。
证体（HOL 同构）：`LAST p` 是商层 dart（`mem_list_of_darts_quotient` 正向），
`e_list` 闭包（`list_of_darts_quotient_sym`）给 `eList (LAST p)` 仍是商层 dart，
反向分解出 `p' ∈ parts L r'`、`r' ∈ N` 且 `eList (LAST p) = LAST p'`，
`parts_uniq_nonnil` + flatten 收口。 -/
theorem eListLast {L : fgraph ℕ} {N : List (List Dart)} {r : List Dart}
    (hL : GoodList L) (hnl : normalList L hL N) (hr : r ∈ N)
    (hall : ∀ l ∈ L, l.Nodup) (hend : (hypermapOfList L hL).EdgeNondegenerate)
    {p : List Dart} (hp : p ∈ parts L r) :
    eList p.getLast! ∈ N.flatten := by
  have hnlS : NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hnl
  have hpS : p ∈ Kepler.Text.TameSpine.partsSpine L r := by
    rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine]
    exact hp
  have hpne : p ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r p hp
  -- LAST p 是商层 dart
  have hq : p.getLast! ∈ listOfDarts (Kepler.Text.TameSpine.quotientListSpine L N) :=
    (Kepler.Text.TameSpine.memListOfDartsQuotient L hL hnlS hend hall _).mpr
      ⟨p, r, hpS, hr, rfl⟩
  -- e_list 闭包：eList (LAST p) 仍是商层 dart
  have he := Kepler.Text.TameSpine.listOfDartsQuotientSym L hL hnlS hend hall _ hq
  -- 反向分解：eList (LAST p) = LAST p'，p' ∈ parts L r'，r' ∈ N
  obtain ⟨p', r', hp', hr', hlast'⟩ :=
    (Kepler.Text.TameSpine.memListOfDartsQuotient L hL hnlS hend hall _).mp he
  have hp'S : p' ∈ Kepler.Text.TameSpine.partsSpine L r' := hp'
  have hp' : p' ∈ parts L r' := by
    rw [Kepler.Text.ChainBridge.parts_eq_partsSpine]
    exact hp'S
  rw [hlast']
  obtain ⟨-, -, -, hp'ne, hsub⟩ :=
    Kepler.Text.MoreLemma2Island3.partsUniqNonnil L hL hnl hr' hp'
  exact List.mem_flatten.mpr ⟨r', hr', hsub _ (getLastMemAux hp'ne)⟩

/-! ## §2 `marked_final_list_ex`（MEEIXJO.hl:54-:61） -/

/-- **HOL `marked_final_list_ex`**（MEEIXJO.hl:54-:61）：
`marked_list L N r x ==> final_list L (find_list N (e_list x))`——
`marked_list` 第 7 合取直取。 -/
theorem markedFinalListEx {L : fgraph ℕ} {hL : GoodList L} {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hm : markedList L hL N r x) :
    finalList L (findList N (eList x)) :=
  hm.2.2.2.2.2.2.1

/-! ## §3 `iso_list_final_dart_list`（MEEIXJO.hl:63-:88） -/

/-- **HOL `iso_list_final_dart_list`**（MEEIXJO.hl:63-:88）：
`good_list L /\ normal_list L N /\ isop_list phi (L,N) (L',N') ==>
final_dart_list L' N' = MAP (\u. phi (FST u),phi (SND u)) (final_dart_list L N)`。
证体：`finalDartList` 展开后 `N' = MAP (MAP lift) N`，`filter_map` 把滤子
推进 map，逐面谓词相等由 `iso_list_final_list_eq`（cons 实例：头槽 s、
尾 N）给出，flatten/map 交换（`MAP_flatten`）收口。 -/
theorem isoListFinalDartList {L L' : fgraph ℕ} {N N' : List (List Dart)}
    (hL : GoodList L) (hn : NormalListSpine hL N) {phi : ℕ → ℕ}
    (hisop : Kepler.Text.TameSpine.IsopListSpine phi L L' N N') :
    finalDartList L' N' =
      (finalDartList L N).map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) := by
  obtain ⟨hinj, hLmap, hNmap⟩ := hisop
  unfold finalDartList
  rw [hNmap, List.filter_map]
  have hq : N.filter ((fun r => decide (finalList L' r)) ∘
      (fun s : List (ℕ × ℕ) => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))
      = N.filter (fun s => decide (finalList L s)) := by
    refine List.filter_congr ?_
    intro s hs
    show decide (finalList L' (s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) =
      decide (finalList L s)
    have hiso : Kepler.Text.TameSpine.IsoListSpine L L' (s :: N)
        (s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) ::
          N.map (fun s' => s'.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) :=
      ⟨phi, hinj, hLmap, rfl⟩
    have hiff := Kepler.Text.TameSpine.isoListFinalListEqSpine hiso hn hs
    have hiff' : finalList L' (s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) ↔
        finalList L s := hiff
    by_cases h : finalList L s
    · rw [decide_eq_true h, decide_eq_true (hiff'.mpr h)]
    · rw [decide_eq_false h, decide_eq_false (fun hc => h (hiff'.mp hc))]
  rw [hq, ← Kepler.Text.TameSpine.mapFlattenSpine
    (f := fun u : ℕ × ℕ => (phi u.1, phi u.2))]

/-! ## §4 `inj_on_contour_condition`（MEEIXJO.hl:90-:140） -/

/-- **HOL `inj_on_contour_condition`**（MEEIXJO.hl:90-:140）：
`good_list L /\ normal_list L N /\ iso_list (L,N) (L',N') /\
(!u v. MEM u (final_dart_list L N) /\ MEM v (final_dart_list L N) ==> ?s. 轮廓段)
==> (!u v. MEM u (final_dart_list L' N') /\ MEM v (final_dart_list L' N') ==>
?s. 轮廓段)`。证体：`iso_list_final_dart_list` 把 L' 侧终面 dart 提回 L 侧
（u = lift x、v = lift x'），L 侧段的 `MAP lift` 像由 `inj_on_contour_list`
给轮廓性，两端由 headD/getLastD 沿 map 交换，子集沿 `iso_list_final_dart_list`
回写。 -/
theorem injOnContourCondition {L L' : fgraph ℕ} {N N' : List (List Dart)}
    (hL : GoodList L) (hn : NormalListSpine hL N)
    (hiso : Kepler.Text.TameSpine.IsoListSpine L L' N N')
    (hcont : ∀ u v, u ∈ finalDartList L N → v ∈ finalDartList L N →
      ∃ s : List Dart, ContourListSpine L s ∧ s ≠ [] ∧ s.headD (0, 0) = u ∧
        s.getLastD (0, 0) = v ∧
        {x : Dart | x ∈ s} ⊆ {x : Dart | x ∈ finalDartList L N}) :
    ∀ u v, u ∈ finalDartList L' N' → v ∈ finalDartList L' N' →
      ∃ s : List Dart, ContourListSpine L' s ∧ s ≠ [] ∧ s.headD (0, 0) = u ∧
        s.getLastD (0, 0) = v ∧
        {x : Dart | x ∈ s} ⊆ {x : Dart | x ∈ finalDartList L' N'} := by
  obtain ⟨phi, hinj, hLmap, hNmap⟩ := hiso
  subst hLmap
  subst hNmap
  have hfd : finalDartList (L.map (List.map phi))
      (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))) =
      (finalDartList L N).map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) :=
    isoListFinalDartList hL hn ⟨hinj, rfl, rfl⟩
  intro u v hu hv
  rw [hfd, List.mem_map] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  obtain ⟨s, hcs, hsne, hhd, hlst, hsub⟩ := hcont x y hx hy
  refine ⟨s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)),
    Kepler.Text.TameSpine.injOnContourList (hL := hL) hinj hcs, ?_, ?_, ?_, ?_⟩
  · -- 非空
    intro hc
    exact hsne (List.map_eq_nil_iff.mp hc)
  · -- headD 沿 map
    rw [← hhd]
    cases s with
    | nil => exact absurd rfl hsne
    | cons a t => rfl
  · -- getLastD 沿 map
    have hlastD : (s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))).getLastD (0, 0)
        = (phi (s.getLastD (0, 0)).1, phi (s.getLastD (0, 0)).2) := by
      rw [List.getLastD_eq_getLast?, List.getLast?_map, List.getLastD_eq_getLast?]
      cases hs : s.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hs) hsne
      | some w => rfl
    rw [hlastD, hlst]
  · -- 子集回写
    intro z hz
    change z ∈ (s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))) at hz
    rw [List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    change (phi w.1, phi w.2) ∈
      finalDartList (L.map (List.map phi))
        (N.map (fun s => s.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))
    rw [hfd, List.mem_map]
    exact ⟨w, hsub hw, rfl⟩

/-! ## §5 `inj_on_contour_condition2`（MEEIXJO.hl:142-:168） -/

/-- **HOL `inj_on_contour_condition2`**（MEEIXJO.hl:142-:168）：
`good_list L /\ normal_list L N /\ iso_list (L,N) (L',N') /\
marked_list L N r x ==> (!u v. MEM u (final_dart_list L' N') /\
MEM v (final_dart_list L' N') ==> ?s. 轮廓段)`。
标记表第 8/9 合取（`final_list L r` 两支）共有同一首合取（终面 dart 两两
之间恒有轮廓段），按 `final_list L r` 二分直取，再 `inj_on_contour_condition`。 -/
theorem injOnContourCondition2 {L L' : fgraph ℕ} {N N' : List (List Dart)}
    {r : List Dart} {x : Dart} (hL : GoodList L) (hn : NormalListSpine hL N)
    (hiso : Kepler.Text.TameSpine.IsoListSpine L L' N N')
    (hm : markedList L hL N r x) :
    ∀ u v, u ∈ finalDartList L' N' → v ∈ finalDartList L' N' →
      ∃ s : List Dart, ContourListSpine L' s ∧ s ≠ [] ∧ s.headD (0, 0) = u ∧
        s.getLastD (0, 0) = v ∧
        {x : Dart | x ∈ s} ⊆ {x : Dart | x ∈ finalDartList L' N'} := by
  have hcont : ∀ u v, u ∈ finalDartList L N → v ∈ finalDartList L N →
      ∃ s : List Dart, ContourListSpine L s ∧ s ≠ [] ∧ s.headD (0, 0) = u ∧
        s.getLastD (0, 0) = v ∧
        {x : Dart | x ∈ s} ⊆ {x : Dart | x ∈ finalDartList L N} := by
    intro u v hu hv
    have hchain : ∃ s : List Dart, Kepler.Text.ChainLists.contourList L s ∧ s ≠ [] ∧
        s.headD (0, 0) = u ∧ s.getLastD (0, 0) = v ∧
        {x : Dart | x ∈ s} ⊆ {x : Dart | x ∈ finalDartList L N} := by
      by_cases hfin : finalList L r
      · exact (hm.2.2.2.2.2.2.2.1 hfin).1 u v hu hv
      · exact (hm.2.2.2.2.2.2.2.2 hfin).1 u v hu hv
    obtain ⟨s, hcs, hsne, hhd, hlst, hsub⟩ := hchain
    exact ⟨s, (Kepler.Text.ChainBridge.contourList_iff_contourListSpine L s).mp hcs,
      hsne, hhd, hlst, hsub⟩
  exact injOnContourCondition hL hn hiso hcont

/-! ## §6 `inj_on_power`（MEEIXJO.hl:171-:195） -/

/-- **HOL `inj_on_power`**（MEEIXJO.hl:171-:195）：
`MEM d r /\ (!x. MEM x r ==> MEM (f x) r) /\ inj_on phi (elements_of_list L) /\
(set_of_list r) SUBSET (darts_of_list L) /\
(!x. MEM x r ==> g (phi (FST x),phi (SND x)) = (phi (FST (f x)),phi (SND (f x))))
==> (g POWER k) (nphi d) = nphi ((f POWER k) d)`。
对 k 归纳：零次 rfl；后继用 `iterate_succ_apply` + 闭包 + 交换方程 + IH。
HOL 证体内 `inj_on`/`SUBSET` 两前提零消费，按原文保留。 -/
theorem injOnPower {phi : ℕ → ℕ} {f g : Dart → Dart} {L : fgraph ℕ}
    {r : List Dart} {d : Dart} (hdr : d ∈ r) (hclo : ∀ x, x ∈ r → f x ∈ r)
    (_hinj : Set.InjOn phi (elementsOfList L))
    (_hsub : {x : Dart | x ∈ r} ⊆ {d : Dart | d ∈ listOfDarts L})
    (hcomm : ∀ x, x ∈ r → g (phi x.1, phi x.2) = (phi (f x).1, phi (f x).2))
    (k : ℕ) :
    (g^[k]) (phi d.1, phi d.2) = (phi ((f^[k]) d).1, phi ((f^[k]) d).2) := by
  have hclos : ∀ j, (f^[j]) d ∈ r := by
    intro j
    induction j with
    | zero => simpa using hdr
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hclo _ ih
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, hcomm _ (hclos k), Function.iterate_succ_apply']

/-! ## §7 `inj_on_normal_list`（MEEIXJO.hl:197-:213） -/

/-- **HOL `inj_on_normal_list`**（MEEIXJO.hl:197-:213）：
`normal_list L N /\ inj_on phi (elements_of_list L) /\ MEM r N ==>
inj_on (\u. phi (FST u),phi(SND u)) (set_of_list r)`——
`normal_list_list_of_darts` 把 `r` 的成员落到 dart 表，
`inj_on_dart_of_list` 的点式本体（`injOnLiftListOfDarts`）收口。 -/
theorem injOnNormalList {L : fgraph ℕ} {hL : GoodList L} {N : List (List Dart)}
    {r : List Dart} (hn : NormalListSpine hL N) {phi : ℕ → ℕ}
    (hinj : Set.InjOn phi (elementsOfList L)) (hr : r ∈ N) :
    Set.InjOn (fun u : ℕ × ℕ => (phi u.1, phi u.2)) {x : Dart | x ∈ r} := by
  intro x hx y hy hxy
  exact Kepler.Text.TameSpine.injOnLiftListOfDarts L hinj
    (Kepler.Text.TameSpine.normalListListOfDarts hn x
      (List.mem_flatten.mpr ⟨r, hr, hx⟩))
    (Kepler.Text.TameSpine.normalListListOfDarts hn y
      (List.mem_flatten.mpr ⟨r, hr, hy⟩)) hxy

/-! ## §8 `inj_on_l_m`（MEEIXJO.hl:215-:281） -/

/-- **HOL `inj_on_l_m`**（MEEIXJO.hl:215-:281）：
`good_list L /\ good_list_nodes L /\ normal_list L N /\ MEM r N /\ MEM d r /\
inj_on phi (elements_of_list L) ==> l'm (MAP (MAP phi) L) (MAP nphi r) (nphi d) = l'm L r d`。
证体：`lm` 两定义集逐点相等——迭代端由 `inj_on_power`（f := next_el r，
g := next_el (r.map lift)，闭包 `next_el_MEM_map`）搬运，`f_list` 端由
`f_list_map`（`fListMap`）搬运，两侧 `minNum` 同集同值。
`good_list_nodes` 前提在 HOL 证体内零消费，按原文保留。 -/
theorem injOnLM {phi : ℕ → ℕ} {L : fgraph ℕ} {N : List (List Dart)} {r : List Dart}
    {d : Dart} (hL : GoodList L) (_hgn : GoodListNodesTl L hL)
    (hn : NormalListSpine hL N) (hr : r ∈ N) (hdr : d ∈ r)
    (hinj : Set.InjOn phi (elementsOfList L)) :
    lm (L.map (List.map phi)) (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))
        (phi d.1, phi d.2)
      = lm L r d := by
  have hrd : ∀ x ∈ r, x ∈ listOfDarts L := fun x hx =>
    Kepler.Text.TameSpine.normalListListOfDarts hn x
      (List.mem_flatten.mpr ⟨r, hr, hx⟩)
  -- nextEl r 迭代保持在 r 内
  have hclos : ∀ j, (nextEl r)^[j] d ∈ r := by
    intro j
    induction j with
    | zero => simpa using hdr
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact nextEl_mem_of_mem ih
  -- lift 在 r 上点式单射
  have hrinj : ∀ u ∈ r, ∀ v ∈ r, (phi u.1, phi u.2) = (phi v.1, phi v.2) → u = v :=
    fun u hu v hv h =>
      Kepler.Text.TameSpine.injOnLiftListOfDarts L hinj (hrd u hu) (hrd v hv) h
  -- 迭代运输
  have hiter : ∀ k : ℕ,
      (nextEl (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))^[k] (phi d.1, phi d.2)
        = (phi ((nextEl r)^[k] d).1, phi ((nextEl r)^[k] d).2) := by
    intro k
    exact injOnPower (f := nextEl r)
      (g := nextEl (r.map fun u : ℕ × ℕ => (phi u.1, phi u.2)))
      (r := r) (d := d) hdr (fun x hx => nextEl_mem_of_mem hx) hinj
      (fun x hx => hrd x hx)
      (fun x hx => Kepler.Text.TameLp.la7_nextEl_map (f := fun u : ℕ × ℕ => (phi u.1, phi u.2))
        (l := r) hrinj hx) k
  -- 两定义集相等
  have hset : {m : ℕ |
        (nextEl (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))^[m + 2] (phi d.1, phi d.2)
          ≠ fList (L.map (List.map phi))
              ((nextEl (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2))))^[m + 1]
                (phi d.1, phi d.2))}
      = {m : ℕ | (nextEl r)^[m + 2] d ≠ fList L ((nextEl r)^[m + 1] d)} := by
    ext m
    simp only [Set.mem_setOf_eq]
    rw [hiter (m + 2), hiter (m + 1),
      Kepler.Text.TameSpine.fListMap (hL := hL) hinj (hrd _ (hclos (m + 1)))]
    constructor
    · intro h hab
      exact h (congrArg (fun z : Dart => (phi z.1, phi z.2)) hab)
    · intro h hab
      exact h (Kepler.Text.TameSpine.injOnLiftListOfDarts L hinj
        (hrd _ (hclos (m + 2)))
        (Kepler.Text.TameSpine.memFList L (hrd _ (hclos (m + 1)))) hab)
  unfold lm
  rw [hset]

/-! ## §9 `inj_on_s_list`（MEEIXJO.hl:283-:323） -/

/-- **HOL `inj_on_s_list`**（MEEIXJO.hl:283-:323）：
`good_list L /\ good_list_nodes L /\ normal_list L N /\ MEM r N /\ MEM d r /\
inj_on phi (elements_of_list L) ==>
s_list (MAP (MAP phi) L) (MAP nphi r) (nphi d) = MAP nphi (s_list L r d)`。
证体：`s_list` 展开后长度槽由 `inj_on_l_m` 给出，逐下标项由 `inj_on_power`
（f := f_list L 在 `list_of_darts L` 上，闭包 `mem_f_list`）搬运，
`MAP_o` 收口。 -/
theorem injOnSList {phi : ℕ → ℕ} {L : fgraph ℕ} {N : List (List Dart)}
    {r : List Dart} {d : Dart} (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hn : NormalListSpine hL N) (hr : r ∈ N) (hdr : d ∈ r)
    (hinj : Set.InjOn phi (elementsOfList L)) :
    sList (L.map (List.map phi)) (r.map (fun u : ℕ × ℕ => (phi u.1, phi u.2)))
        (phi d.1, phi d.2)
      = (sList L r d).map (fun u : ℕ × ℕ => (phi u.1, phi u.2)) := by
  have hrd : ∀ x ∈ r, x ∈ listOfDarts L := fun x hx =>
    Kepler.Text.TameSpine.normalListListOfDarts hn x
      (List.mem_flatten.mpr ⟨r, hr, hx⟩)
  have hdD : d ∈ listOfDarts L := hrd d hdr
  unfold Kepler.Text.ChainLists.sList
  rw [injOnLM hL hgn hn hr hdr hinj]
  have hstep : ((List.range' 1 (lm L r d)).map (fun i => (fList L)^[i] d)).map
      (fun u : ℕ × ℕ => (phi u.1, phi u.2))
      = (List.range' 1 (lm L r d)).map
        (fun i => (fList (L.map (List.map phi)))^[i] (phi d.1, phi d.2)) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro i _
    exact (injOnPower (f := fList L) (g := fList (L.map (List.map phi)))
      (r := listOfDarts L) (d := d) hdD (fun x hx => Kepler.Text.TameSpine.memFList L hx)
      hinj (fun x hx => hx)
      (fun x hx => Kepler.Text.TameSpine.fListMap (hL := hL) hinj hx) i).symm
  exact hstep.symm

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.eListLast
#print axioms Kepler.Text.Reduction1.markedFinalListEx
#print axioms Kepler.Text.Reduction1.isoListFinalDartList
#print axioms Kepler.Text.Reduction1.injOnContourCondition
#print axioms Kepler.Text.Reduction1.injOnContourCondition2
#print axioms Kepler.Text.Reduction1.injOnPower
#print axioms Kepler.Text.Reduction1.injOnNormalList
#print axioms Kepler.Text.Reduction1.injOnLM
#print axioms Kepler.Text.Reduction1.injOnSList
