/-
  Kepler.Text.TameSpine.TameList67 — B3 D 链第八批：RXOKSKC A9 接口件到达
  （RXOKSKC.hl :523-:1105 章末段：hypermap_of_list L 的 iso 有限 list 表示）。
  接续批 66 = TameList66.lean（f7a559d6）。

  ┌─ 本批战绩小结 ────────────────────────────────────────────────
  │（收口时补全）
  └──────────────────────────────────────────────────────────────

  新雷区（本批实测记档，编号承批 66 的 #167）：
  -（收口时补全）

  批 68 接续点：（收口时补全）
-/

import Kepler.Text.TameSpine.TameList66

/-! # RXOKSKC（:523-:1105）：A9 接口件 `iso H (hypermap_of_list L)` -/

namespace Kepler.Text.TameSpine

variable {α : Type*} [DecidableEq α]

open Kepler.Assembly (listPairs nextEl prevEl)
open Kepler.Text.Fan (bijOn_res extendPerm extendPerm_permutes)


omit [DecidableEq α] in
/-- zip 表取元：`(l₁.zip l₂)[i] = (l₁[i], l₂[i])`（Mathlib 无 getElem_zip；
zip-长度前置显式假设，免结论内嵌 by-proof 的调用点统一化雷区 #170）。 -/
private theorem getElem_zip' {l₁ l₂ : List α} {i : ℕ} (h : i < (l₁.zip l₂).length)
    (h1 : i < l₁.length) (h2 : i < l₂.length) :
    (l₁.zip l₂)[i]'h = (l₁[i]'h1, l₂[i]'h2) := by
  induction l₁ generalizing l₂ i with
  | nil => cases l₂ <;> simp at h
  | cons a t ih =>
    cases l₂ with
    | nil => simp at h2
    | cons b t' =>
      cases i with
      | zero => simp
      | succ i' =>
        rw [List.zip_cons_cons] at h
        show ((a, b) :: (t.zip t'))[i' + 1]'h
            = ((a :: t)[i' + 1]'(by simpa using h1), (b :: t')[i' + 1]'(by simpa using h2))
        rw [List.getElem_cons, List.getElem_cons, List.getElem_cons]
        exact ih (by simpa using h) (by simpa using h1) (by simpa using h2)

omit [DecidableEq α] in
/-- list_pairs 专用 zip 取元包装（listPairs 正语法直给，免调用点
delta-unification 雷区 #170）。 -/
private theorem getElemListPairs {s : List α} {j : ℕ} (h1 : j < s.length)
    (h2 : j < (s.drop 1 ++ s.take 1).length) :
    (listPairs s)[j]'(by
      show j < (s.zip (s.drop 1 ++ s.take 1)).length
      rw [List.length_zip]
      exact lt_min_iff.mpr ⟨h1, h2⟩)
      = (s[j]'h1, (s.drop 1 ++ s.take 1)[j]'h2) :=
  getElem_zip' (by
    show j < (s.zip (s.drop 1 ++ s.take 1)).length
    rw [List.length_zip]
    exact lt_min_iff.mpr ⟨h1, h2⟩) h1 h2

omit [DecidableEq α] in
/-- zip 表成员的取元构造型：第 i 位逐坐标相等 ⟹ 成员。 -/
private theorem mem_zip_of {l₁ l₂ : List α} {p : α × α} {i : ℕ}
    (h1 : i < l₁.length) (h2 : i < l₂.length) (e1 : l₁[i]'h1 = p.1) (e2 : l₂[i]'h2 = p.2) :
    p ∈ l₁.zip l₂ := by
  have hk := getElem_zip' (by rw [List.length_zip]; omega) h1 h2
  have hp : p = (l₁[i]'h1, l₂[i]'h2) :=
    Prod.ext (y := (l₁[i]'h1, l₂[i]'h2)) e1.symm e2.symm
  rw [hp, ← hk]
  have hlen : i < (l₁.zip l₂).length := by
    rw [List.length_zip]
    omega
  exact List.getElem_mem hlen

/-! ### §1 底座一：bijOn 群泛型化（TameLp:3870-3989 机理照搬，
fgraph ℕ 专件 → 泛型 α；参数化 {L} (hn : (rxListOfDarts L).Nodup)） -/

/-- find? 无命中 ⟹ rxFindFace 空表（TameLp findFaceDarts_none 泛型化）。 -/
private theorem rxFindFace_none {L : List (List α)} {d : α × α}
    (hval : (L.find? fun l => decide (d ∈ listPairs l)) = none) :
    rxFindFace L d = [] := by
  unfold rxFindFace
  rw [hval]
  rfl

/-- find? 命中 l' ⟹ rxFindFace = listPairs l' 且 d 落其中
（TameLp findFaceDarts_some 泛型化）。 -/
private theorem rxFindFace_some {L : List (List α)} {d : α × α} {l' : List α}
    (hfeq : (L.find? fun l => decide (d ∈ listPairs l)) = some l') :
    rxFindFace L d = listPairs l' ∧ d ∈ listPairs l' := by
  constructor
  · unfold rxFindFace
    rw [hfeq]
    rfl
  · exact of_decide_eq_true
      (List.find?_some (p := fun l => decide (d ∈ listPairs l)) hfeq)

/-- 面列表 dart 自反件（TameLp dart_in_face 泛型化）：
`d ∈ rxFindFace L d ↔ d ∈ rxListOfDarts L`。 -/
theorem rxDartInFindFace (L : List (List α)) (d : α × α) :
    d ∈ rxFindFace L d ↔ d ∈ rxListOfDarts L := by
  by_cases hval : (L.find? fun l => decide (d ∈ listPairs l)) = none
  · rw [rxFindFace_none hval]
    constructor
    · intro hm
      exact absurd hm (by simp)
    · intro hm
      obtain ⟨l, hl, hdl⟩ := rxMemListDarts.mp hm
      exact absurd hdl (by simpa using List.find?_eq_none.mp hval l hl)
  · obtain ⟨l', hfeq⟩ := Option.ne_none_iff_exists.mp hval
    obtain ⟨heq, hd⟩ := rxFindFace_some hfeq.symm
    rw [heq]
    constructor
    · intro hm
      exact rxMemListDarts.mpr ⟨l', List.mem_of_find?_eq_some hfeq.symm, hm⟩
    · intro hm
      exact hd

/-- 落面列表 ⟹ 落 dart 表（TameLp mem_darts_of_mem_findFace 泛型化）。 -/
theorem rxMemDarts_of_mem_rxFindFace {L : List (List α)} {z : α × α} {d : α × α}
    (hz : z ∈ rxFindFace L d) : z ∈ rxListOfDarts L := by
  unfold rxFindFace at hz
  rcases Option.eq_none_or_eq_some (L.find? fun l => decide (d ∈ listPairs l)) with hval |
    ⟨l', hfeq⟩
  · rw [hval] at hz
    simp [listPairs] at hz
  · rw [hfeq] at hz
    exact rxMemListDarts.mpr ⟨l', List.mem_of_find?_eq_some hfeq, hz⟩

/-- 自身面列表的自描述形（TameLp findFaceDarts_ex_of_self 泛型化）。 -/
private theorem rxFindFace_ex_of_self {L : List (List α)} {z : α × α}
    (hz : z ∈ rxFindFace L z) :
    ∃ l : List α, l ∈ L ∧ rxFindFace L z = listPairs l ∧ z ∈ listPairs l := by
  by_cases hval : (L.find? fun l => decide (z ∈ listPairs l)) = none
  · rw [rxFindFace_none hval] at hz
    simp at hz
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : (L.find? fun l => decide (z ∈ listPairs l)) = some l' := hl''.symm
    obtain ⟨heq, hzl'⟩ := rxFindFace_some hfeq
    exact ⟨l', List.mem_of_find?_eq_some hfeq, heq, hzl'⟩

/-- 命中唯一性（TameLp findFaceDarts_eq_of_mem 泛型化）：d 落某面片的
pair 列表 ⟹ findFace 命中的就是该列表。 -/
private theorem rxFindFace_eq_of_mem {L : List (List α)} (hn : (rxListOfDarts L).Nodup)
    {l : List α} (hl : l ∈ L) {d : α × α} (hd : d ∈ listPairs l) :
    rxFindFace L d = listPairs l := by
  have hflat : ((L.map listPairs).flatten).Nodup := hn
  by_cases hval : (L.find? fun l => decide (d ∈ listPairs l)) = none
  · rw [List.find?_eq_none] at hval
    have hnc := hval l hl
    simp at hnc
    exact absurd hd hnc
  · obtain ⟨l', hl''⟩ := Option.ne_none_iff_exists.mp hval
    have hfeq : (L.find? fun l => decide (d ∈ listPairs l)) = some l' := hl''.symm
    obtain ⟨heq, hdl'⟩ := rxFindFace_some hfeq
    rw [heq]
    refine TameLp.flatten_nodup_inj hflat (List.mem_map.mpr
      ⟨l', List.mem_of_find?_eq_some hfeq, rfl⟩)
      (List.mem_map.mpr ⟨l, hl, rfl⟩) hdl' hd

/-- 面列表相容（TameLp findFaceDarts_congr_of_mem 泛型化）：同处一面的两个
dart 有相同 findFace。 -/
theorem rxFindFace_congr_of_mem {L : List (List α)} (hn : (rxListOfDarts L).Nodup)
    {z d : α × α} (hd : d ∈ rxListOfDarts L) (hz : z ∈ rxFindFace L d) :
    rxFindFace L z = rxFindFace L d := by
  have hz' : z ∈ rxFindFace L z := (rxDartInFindFace L z).mpr
    (rxMemDarts_of_mem_rxFindFace hz)
  have hd' : d ∈ rxFindFace L d := (rxDartInFindFace L d).mpr hd
  obtain ⟨l1, hl1, e1, hd1⟩ := rxFindFace_ex_of_self hz'
  obtain ⟨l0, hl0, e0, _⟩ := rxFindFace_ex_of_self hd'
  have hz0 : z ∈ listPairs l0 := by rw [← e0]; exact hz
  have hpl : listPairs l1 = listPairs l0 :=
    TameLp.flatten_nodup_inj hn (List.mem_map.mpr ⟨l1, hl1, rfl⟩)
      (List.mem_map.mpr ⟨l0, hl0, rfl⟩) hd1 hz0
  rw [e1, hpl, ← e0]

/-- 面列表无重（TameLp findFaceDarts_nodup 泛型化）。 -/
theorem rxFindFace_nodup {L : List (List α)} (hn : (rxListOfDarts L).Nodup)
    (d : α × α) : (rxFindFace L d).Nodup := by
  unfold rxFindFace
  rcases Option.eq_none_or_eq_some (L.find? fun l => decide (d ∈ listPairs l)) with hval |
    ⟨l', hfeq⟩
  · rw [hval]
    simp [listPairs]
  · rw [hfeq]
    exact TameLp.flatten_nodup_mem hn (List.mem_map.mpr
      ⟨l', List.mem_of_find?_eq_some hfeq, rfl⟩)

/-! ### §1.1 fList / nList / eSwap 侧（TameLp:3914-3989 机理照搬） -/

/-- f_list 保 dart（TameLp fList_mem_darts 泛型化）。 -/
theorem rxFList_mem_darts {L : List (List α)} (_hn : (rxListOfDarts L).Nodup)
    {d : α × α} (hd : d ∈ rxListOfDarts L) : rxFList L d ∈ rxListOfDarts L :=
  rxMemDarts_of_mem_rxFindFace
    (TameLp.nextEl_mem_of_mem ((rxDartInFindFace L d).mpr hd))

/-- rxFindFace 在 f_list 下不变（TameLp findFace_fList 泛型化）。 -/
theorem rxFindFace_rxFList {L : List (List α)} (hn : (rxListOfDarts L).Nodup)
    {d : α × α} (hd : d ∈ rxListOfDarts L) :
    rxFindFace L (rxFList L d) = rxFindFace L d :=
  rxFindFace_congr_of_mem hn hd
    (TameLp.nextEl_mem_of_mem ((rxDartInFindFace L d).mpr hd))

/-- prev-next 逆之一（TameLp fList_prev_inverse 泛型化）。 -/
theorem rxFList_rxFindFace_prev_inverse {L : List (List α)}
    (hn : (rxListOfDarts L).Nodup) {d : α × α} (hd : d ∈ rxListOfDarts L) :
    rxFList L (prevEl (rxFindFace L d) d) = d := by
  have hdn : d ∈ rxFindFace L d := (rxDartInFindFace L d).mpr hd
  show nextEl (rxFindFace L (prevEl (rxFindFace L d) d))
      (prevEl (rxFindFace L d) d) = d
  rw [show rxFindFace L (prevEl (rxFindFace L d) d) = rxFindFace L d from
    rxFindFace_congr_of_mem hn hd (TameLp.prevEl_mem_of_mem hdn)]
  exact TameLp.nextEl_prevEl (rxFindFace_nodup hn d) hdn

/-- prev-next 逆之二（TameLp prev_fList_inverse 泛型化）。 -/
theorem prev_rxFindFace_inverse {L : List (List α)} (hn : (rxListOfDarts L).Nodup)
    {d : α × α} (hd : d ∈ rxListOfDarts L) :
    prevEl (rxFindFace L (rxFList L d)) (rxFList L d) = d := by
  rw [rxFindFace_rxFList hn hd]
  exact TameLp.prevEl_nextEl (rxFindFace_nodup hn d) ((rxDartInFindFace L d).mpr hd)

omit [DecidableEq α] in
/-- e_list 单射（TameLp eList_inj 泛型化）。 -/
theorem rxESwap_inj {a b : α × α} (h : rxESwap a = rxESwap b) : a = b := by
  have h1 : a.2 = b.2 := congrArg Prod.fst h
  have h2 : a.1 = b.1 := congrArg Prod.snd h
  exact Prod.ext h2 h1

/-- n_list ∘ f_list = e_list（TameLp nList_fList 泛型化）。 -/
theorem rxNList_rxFList {L : List (List α)} (hn : (rxListOfDarts L).Nodup)
    {d : α × α} (hd : d ∈ rxListOfDarts L) : rxNList L (rxFList L d) = rxESwap d := by
  show rxESwap (prevEl (rxFindFace L (rxFList L d)) (rxFList L d)) = _
  rw [rxFindFace_rxFList hn hd]
  exact congrArg rxESwap (TameLp.prevEl_nextEl (rxFindFace_nodup hn d)
    ((rxDartInFindFace L d).mpr hd))

omit [DecidableEq α] in
/-- eSwap 的 bijOn（TameLp bijOn_eList 泛型化，good_list 第三件直供）。 -/
theorem bijOn_rxESwap {L : List (List α)} (hL : rxGoodList L) :
    Set.BijOn rxESwap {d | d ∈ rxListOfDarts L} {d | d ∈ rxListOfDarts L} :=
  ⟨fun d hd => hL.2.2 d hd, fun _a _ha _b _hb heq => rxESwap_inj heq,
    fun y hy => ⟨rxESwap y, hL.2.2 y hy, rfl⟩⟩

/-- f_list 的 bijOn（TameLp bijOn_fList 泛型化）。 -/
theorem bijOn_rxFList {L : List (List α)} (hn : (rxListOfDarts L).Nodup) :
    Set.BijOn (rxFList L) {d | d ∈ rxListOfDarts L} {d | d ∈ rxListOfDarts L} := by
  refine ⟨fun d hd => rxFList_mem_darts hn hd, fun a ha b hb heq => ?_, fun y hy => ?_⟩
  · have hla := prev_rxFindFace_inverse hn ha
    have hlb := prev_rxFindFace_inverse hn hb
    calc a = prevEl (rxFindFace L (rxFList L a)) (rxFList L a) := hla.symm
      _ = prevEl (rxFindFace L (rxFList L b)) (rxFList L b) :=
            congrArg (fun z => prevEl (rxFindFace L z) z) heq
      _ = b := hlb
  · exact ⟨prevEl (rxFindFace L y) y,
      rxMemDarts_of_mem_rxFindFace (TameLp.prevEl_mem_of_mem
        ((rxDartInFindFace L y).mpr hy)),
      rxFList_rxFindFace_prev_inverse hn hy⟩

/-- n_list 的 bijOn（TameLp bijOn_nList 泛型化）。 -/
theorem bijOn_rxNList {L : List (List α)} (hL : rxGoodList L) :
    Set.BijOn (rxNList L) {d | d ∈ rxListOfDarts L} {d | d ∈ rxListOfDarts L} := by
  have hn : (rxListOfDarts L).Nodup := hL.1
  refine ⟨fun d hd => ?_, fun a ha b hb heq => ?_, fun y hy => ?_⟩
  · show rxESwap (prevEl (rxFindFace L d) d) ∈ rxListOfDarts L
    exact hL.2.2 _ (rxMemDarts_of_mem_rxFindFace (TameLp.prevEl_mem_of_mem
      ((rxDartInFindFace L d).mpr hd)))
  · change rxESwap (prevEl (rxFindFace L a) a)
      = rxESwap (prevEl (rxFindFace L b) b) at heq
    have hprev : prevEl (rxFindFace L a) a = prevEl (rxFindFace L b) b :=
      rxESwap_inj heq
    have k1 : rxFList L (prevEl (rxFindFace L a) a) = a := rxFList_rxFindFace_prev_inverse hn ha
    have k2 : rxFList L (prevEl (rxFindFace L b) b) = b := rxFList_rxFindFace_prev_inverse hn hb
    calc a = rxFList L (prevEl (rxFindFace L a) a) := k1.symm
      _ = rxFList L (prevEl (rxFindFace L b) b) := by rw [hprev]
      _ = b := k2
  · refine ⟨rxFList L (rxESwap y), rxFList_mem_darts hn (hL.2.2 y hy), ?_⟩
    show rxNList L (rxFList L (rxESwap y)) = y
    rw [rxNList_rxFList hn (d := rxESwap y) (hL.2.2 y hy)]
    rfl

/-! ### §2 底座二：hypermapOfListG 构造（TameLp:3993-4048 机理照搬，
hypermap_of_list 泛型 α 层首落；构造条件化于 rxGoodList——HOL 的
hypermap_of_list 全域 total 而 Lean 的 Hypermap 三置换须 Equiv.Perm，
rxGoodListNodes 相应参数化记档） -/

/-- HOL `hypermap_of_list`（list_hypermap-compiled.hl:60-62）泛型 α 层：
dart 表的 Finset 上升为 dart 集，三映射经 extendPerm 延拓。 -/
noncomputable def hypermapOfListG {α : Type*} [DecidableEq α] (L : List (List α))
    (hL : rxGoodList L) : Hypermap (α × α) :=
  have hN : (rxListOfDarts L).Nodup := hL.1
  have hsd : ((rxListOfDarts L).toFinset : Set (α × α)) = {d | d ∈ rxListOfDarts L} := by
    ext d
    exact List.mem_toFinset
  have hbe' := bijOn_res (fs := (rxListOfDarts L).toFinset)
    (s := {d | d ∈ rxListOfDarts L}) hsd (bijOn_rxESwap hL)
  have hbn' := bijOn_res (fs := (rxListOfDarts L).toFinset)
    (s := {d | d ∈ rxListOfDarts L}) hsd (bijOn_rxNList hL)
  have hbf' := bijOn_res (fs := (rxListOfDarts L).toFinset)
    (s := {d | d ∈ rxListOfDarts L}) hsd (bijOn_rxFList hN)
  { darts := (rxListOfDarts L).toFinset
    edgeMap := extendPerm (rxListOfDarts L).toFinset rxESwap hbe'
    nodeMap := extendPerm (rxListOfDarts L).toFinset (rxNList L) hbn'
    faceMap := extendPerm (rxListOfDarts L).toFinset (rxFList L) hbf'
    edgeMap_permutes := extendPerm_permutes
    nodeMap_permutes := extendPerm_permutes
    faceMap_permutes := extendPerm_permutes
    comp_eq_one := by
      refine Equiv.Perm.ext fun d => ?_
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      by_cases hd : d ∈ ((rxListOfDarts L).toFinset : Set (α × α))
      · have hd' : d ∈ rxListOfDarts L := List.mem_toFinset.mp hd
        have hfd : rxFList L d ∈ ((rxListOfDarts L).toFinset : Set (α × α)) :=
          List.mem_toFinset.mpr (rxFList_mem_darts hN hd')
        have hnd : rxNList L (rxFList L d) ∈ ((rxListOfDarts L).toFinset : Set (α × α)) :=
          List.mem_toFinset.mpr (by rw [rxNList_rxFList hN hd']; exact hL.2.2 d hd')
        simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hd, hfd, hnd,
          if_true]
        rw [rxNList_rxFList hN hd']
        rfl
      · simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hd, if_false] }

/-- dart 集四槽之一：dart 集即 dart 表。 -/
theorem darts_hypermapOfListG {α : Type*} [DecidableEq α] (L : List (List α))
    (hL : rxGoodList L) :
    (↑(hypermapOfListG L hL).darts : Set (α × α)) = {d | d ∈ rxListOfDarts L} := by
  ext d
  exact List.mem_toFinset

/-- 映射四槽之二：edgeMap = e_list（dart 上）。 -/
theorem edgeMap_hypermapOfListG {α : Type*} [DecidableEq α] (L : List (List α))
    (hL : rxGoodList L) {d : α × α} (hd : d ∈ (hypermapOfListG L hL).darts) :
    (hypermapOfListG L hL).edgeMap d = rxESwap d := by
  have hd' : d ∈ ((rxListOfDarts L).toFinset : Set (α × α)) := hd
  unfold hypermapOfListG
  simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hd', if_true]

/-- 映射四槽之三：nodeMap = n_list（dart 上）。 -/
theorem nodeMap_hypermapOfListG {α : Type*} [DecidableEq α] (L : List (List α))
    (hL : rxGoodList L) {d : α × α} (hd : d ∈ (hypermapOfListG L hL).darts) :
    (hypermapOfListG L hL).nodeMap d = rxNList L d := by
  have hd' : d ∈ ((rxListOfDarts L).toFinset : Set (α × α)) := hd
  unfold hypermapOfListG
  simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hd', if_true]

/-- 映射四槽之四：faceMap = f_list（dart 上）。 -/
theorem faceMap_hypermapOfListG {α : Type*} [DecidableEq α] (L : List (List α))
    (hL : rxGoodList L) {d : α × α} (hd : d ∈ (hypermapOfListG L hL).darts) :
    (hypermapOfListG L hL).faceMap d = rxFList L d := by
  have hd' : d ∈ ((rxListOfDarts L).toFinset : Set (α × α)) := hd
  unfold hypermapOfListG
  simp only [extendPerm, Equiv.ofBijective_apply, Kepler.Text.Fan.res, hd', if_true]

/-! ### §2.1 good_list_nodes 泛型形（tame_defs2.hl:39-42；list_hypermap-
compiled.hl:66-67） -/

/-- HOL `list_of_elements`（list_hypermap-compiled.hl:28，`undup (flatten L)`；
Lean 侧 undup ↦ List.dedup）。 -/
def rxListOfElements (L : List (List α)) : List α := L.flatten.dedup

/-- HOL `elements_of_list`（list_hypermap-compiled.hl:29）。 -/
def rxElementsOfList (L : List (List α)) : Set α := {x | x ∈ rxListOfElements L}

/-- HOL `set_of_list (nodes_of_list L)`（FST-fiber 集，
list_hypermap-compiled.hl:30-32 + set_nodes_of_list 同面）。 -/
def rxNodesOfListSet (L : List (List α)) : Set (Set (α × α)) :=
  (fun x : α => {d | d ∈ rxListOfDarts L ∧ d.1 = x}) '' rxElementsOfList L

/-- HOL `good_list_nodes`（tame_defs2.hl:39-42）泛型 α 层，构造条件化：
`node_set (hypermap_of_list L) = set_of_list (nodes_of_list L)`。
（HOL 的 hypermap_of_list 全域 total；Lean 侧 Hypermap 三映射须 Equiv.Perm，
故节点集在 rxGoodList L 的构造证明下取——语句偏差记档，Assembly.GoodListNodes
True 桩属 W0 S11 忠实化待办不动。） -/
def rxGoodListNodes {α : Type*} [DecidableEq α] (L : List (List α)) (hL : rxGoodList L) :
    Prop := (hypermapOfListG L hL).nodeSet = rxNodesOfListSet L


/-! ### §3 缺口底座（RXOKSKC 大证消费件；HOL DART_EQ_UNIONS /
FINITE_ORBIT_MAP / iterate_map_valuation / HYP_MAPS_INVS 零在册重推导）
+ list 链路 helper（nextEl/prevEl 的取元形与 list_pairs 的 next/prev 识别） -/

/-! #### §3.1 DART_EQ_UNIONS（Hypermap_and_fan.hl：dart = ⋃ 三轨道集） -/

/-- dart 集 = 三映射轨道集之并（泛型引擎件）。 -/
theorem darts_eq_iUnion_setOfOrbits {α : Type*} [DecidableEq α] (H : Hypermap α)
    (f : Equiv.Perm α) (hf : PermutesOn f H.darts) :
    (↑H.darts : Set α) = ⋃₀ (setOfOrbits H.darts f) := by
  ext y
  constructor
  · intro hy
    refine Set.mem_sUnion.mpr ⟨orbitMap f y,
      (Hypermap.PermutesOn.mem_iff_orbitMap_mem_setOfOrbits hf y).mp hy,
      mem_orbitMap_self f y⟩
  · intro hy
    obtain ⟨N, hN, hyN⟩ := Set.mem_sUnion.mp hy
    obtain ⟨x, hx, rfl⟩ := hN
    exact orbitMap_subset_of_permutesOn hf hx hyN

/-- **HOL `DART_EQ_UNIONS`**（Hypermap_and_fan.hl，face 槽）。 -/
theorem darts_eq_iUnion_faceSet (H : Hypermap α) :
    (↑H.darts : Set α) = ⋃₀ H.faceSet :=
  darts_eq_iUnion_setOfOrbits H H.faceMap H.faceMap_permutes

/-- **HOL `DART_EQ_UNIONS`**（node 槽）。 -/
theorem darts_eq_iUnion_nodeSet (H : Hypermap α) :
    (↑H.darts : Set α) = ⋃₀ H.nodeSet :=
  darts_eq_iUnion_setOfOrbits H H.nodeMap H.nodeMap_permutes

/-- **HOL `DART_EQ_UNIONS`**（edge 槽）。 -/
theorem darts_eq_iUnion_edgeSet (H : Hypermap α) :
    (↑H.darts : Set α) = ⋃₀ H.edgeSet :=
  darts_eq_iUnion_setOfOrbits H H.edgeMap H.edgeMap_permutes

/-! #### §3.2 iterate_map_valuation + FINITE_ORBIT_MAP 形 -/

/-- **HOL `Hypermap.iterate_map_valuation`**：`p (p^n x) = p^(n+1) x`
（一步 `pow_succ'`）。 -/
theorem iterateMapValuation {α : Type*} (f : Equiv.Perm α) (n : ℕ) (x : α) :
    f ((f ^ n) x) = (f ^ (n + 1)) x := by
  rw [show (f ^ (n + 1)) = f * f ^ n from pow_succ' f n, Equiv.Perm.mul_apply]

/-- 面周期折算：`f^m x = x`（m ≠ 0）⟹ `f^(k % m) x = f^k x`。 -/
theorem pow_mod_eq {α : Type*} {f : Equiv.Perm α} {x : α} {m : ℕ} (_hm : m ≠ 0)
    (h : (f ^ m) x = x) (k : ℕ) : (f ^ (k % m)) x = (f ^ k) x := by
  have hfix : (f ^ (m * (k / m))) x = x := by
    rw [pow_mul]
    exact pow_fix_pow f h (k / m)
  calc (f ^ (k % m)) x = (f ^ (k % m)) ((f ^ (m * (k / m))) x) := by rw [hfix]
    _ = (f ^ (k % m + m * (k / m))) x := by
        rw [pow_add, Equiv.Perm.mul_apply]
    _ = (f ^ k) x := by
        rw [show k % m + m * (k / m) = k from Nat.mod_add_div k m]

/-- **HOL `Hypermap_and_fan.FINITE_ORBIT_MAP`** 的 Lean 拼合形（face 槽）：
面轨道 = 指标 < CARD (face) 的幂像（`orbit_cyclic` + `pow_card_face_apply_self`）。 -/
theorem face_eq_orbit_range (H : Hypermap α) (y : α) :
    H.face y = (fun k : ℕ => (H.faceMap ^ k) y) '' ↑(Finset.range (H.face y).ncard) := by
  have hpos : 0 < (H.face y).ncard := by
    show 0 < (orbitMap H.faceMap y).ncard
    rw [Set.ncard_pos (orbitMap_finite H.faceMap_permutes y)]
    exact ⟨y, mem_orbitMap_self H.faceMap y⟩
  exact orbit_cyclic H.faceMap (by omega) (H.pow_card_face_apply_self y)

/-! #### §3.3 HYP_MAPS_INVS（Lvducxu 六合取；Equiv 逆元恒等式） -/

/-- **HOL `Lvducxu.HYP_MAPS_INVS`**（LocalAuto10:346 六合取）。 -/
theorem hypMapsInvs (H : Hypermap α) (x : α) :
    H.edgeMap (H.edgeMap.symm x) = x ∧ H.edgeMap.symm (H.edgeMap x) = x ∧
      H.faceMap (H.faceMap.symm x) = x ∧ H.faceMap.symm (H.faceMap x) = x ∧
      H.nodeMap (H.nodeMap.symm x) = x ∧ H.nodeMap.symm (H.nodeMap x) = x := by
  simp

/-! #### §3.4 nextEl / prevEl 取元形 + list_pairs 的 next / prev 识别
（TameList10 原子式证法照搬泛型化：`(listPairs s).idxOf (x,y)` 整体作 atom，
getElemConN67 做取元指标迁移，不拆 ite——雷区 #169/#171 的根治） -/

omit [DecidableEq α] in
/-- 同表两下标相等则取元相等（proof-irrelevant getElem 换形器；
TameList10 getElemConN 同体泛型化）。 -/
private theorem getElemConN67 {α : Type*} {l : List α} {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (hab : a = b) : l[a]'ha = l[b]'hb := by
  subst hab; rfl

/-- `prevEl` 的 idxOf 原子式取元形（不拆 ite）。 -/
theorem prevEl_eq_getD_idxOf {l : List α} {x : α} (hmem : x ∈ l) :
    prevEl l x = l.getD ((l.idxOf x + l.length - 1) % l.length) x := by
  unfold prevEl
  rw [if_neg (show ¬(x ∉ l) from by simp [hmem])]
  by_cases h0 : l.idxOf x = 0
  · rw [if_pos h0, TameLp.li_getLastD_getD (List.length_pos_of_mem hmem) x, h0,
      Nat.zero_add,
      Nat.mod_eq_of_lt (by have := List.length_pos_of_mem hmem; omega)]
  · have hilt : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hmem
    rw [if_neg h0,
      show (l.idxOf x + l.length - 1) % l.length = l.idxOf x - 1 from by
        have hz : l.idxOf x + l.length - 1 = (l.idxOf x - 1) + l.length := by omega
        rw [hz, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)]

omit [DecidableEq α] in
/-- rot1 列长度 = 原列长度。 -/
private theorem rot1_length (L : List α) :
    (L.drop 1 ++ L.take 1).length = L.length := by
  cases L with
  | nil => simp
  | cons a t => simp

omit [DecidableEq α] in
/-- rot1 下标折算（T66 getElem_rot1 同面，? -form）。 -/
private theorem getElem_rot1 (L : List α) (i : ℕ) (hi : i < L.length) :
    (L.drop 1 ++ L.take 1)[i]? = L[(i + 1) % L.length]? := by
  rcases Nat.lt_or_ge i (L.length - 1) with hlt | hge
  · have h1 : i < (L.drop 1).length := by
      simp only [List.length_drop]; omega
    rw [List.getElem?_append_left h1, List.getElem?_drop,
      show (i + 1) % L.length = i + 1 from Nat.mod_eq_of_lt (by omega),
      Nat.add_comm 1 i]
  · have hilen : i = L.length - 1 := by omega
    have h2 : (L.drop 1).length ≤ i := by
      simp only [List.length_drop]; omega
    rw [List.getElem?_append_right h2,
      show i - (L.drop 1).length = 0 by simp only [List.length_drop]; omega,
      List.getElem?_take_of_lt (by omega),
      show (i + 1) % L.length = 0 from by
        rw [show i + 1 = L.length from by omega]
        exact Nat.mod_self (L.length)]

omit [DecidableEq α] in
/-- rot1 下标折算的 `'h` 形（T66 getElem_rot1 同面）。 -/
private theorem getElem_rot1' (L : List α) {i : ℕ}
    (hi : i < (L.drop 1 ++ L.take 1).length) :
    (L.drop 1 ++ L.take 1)[i]'hi
      = L[(i + 1) % L.length]'(by
          have hi' : i < L.length := by rw [← rot1_length]; exact hi
          exact Nat.mod_lt _ (by omega : 0 < L.length)) := by
  have hilen : i < L.length := by rw [← rot1_length]; exact hi
  have hpos : 0 < L.length := by omega
  have hmod : (i + 1) % L.length < L.length := Nat.mod_lt _ hpos
  have h1 : (L.drop 1 ++ L.take 1)[i]? = some ((L.drop 1 ++ L.take 1)[i]'hi) :=
    List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩
  have h2 : L[(i + 1) % L.length]? = some (L[(i + 1) % L.length]'hmod) :=
    List.getElem?_eq_some_iff.mpr ⟨hmod, rfl⟩
  have h3 := getElem_rot1 L i hilen
  rw [h1, h2] at h3
  exact Option.some.inj h3

/-- **HOL `next_el_list_pairs`**（list_hypermap-compiled.hl:316）泛型 α 层：
`(x,y) ∈ list_pairs s` 且 s 无重 ⟹ `next_el (list_pairs s) (x,y) = (y, next_el s y)`。
（TameList10 nextElListPairs 的泛型化；ℕ 专件在册，同名雷区 #157 分装 G 后缀。） -/
theorem nextElListPairsG {s : List α} (hn : s.Nodup) {x y : α} (hp : (x, y) ∈ listPairs s) :
    nextEl (listPairs s) (x, y) = (y, nextEl s y) := by
  have hlen : (listPairs s).length = s.length := by
    show (s.zip (s.drop 1 ++ s.take 1)).length = s.length
    rw [List.length_zip, rot1_length, Nat.min_self]
  have hpos : 0 < (listPairs s).length := List.length_pos_of_mem hp
  have hposl : 0 < s.length := by rw [← hlen]; exact hpos
  have hk : (listPairs s).idxOf (x, y) < (listPairs s).length :=
    List.idxOf_lt_length_iff.mpr hp
  have hkL : (listPairs s).idxOf (x, y) < s.length := by rw [← hlen]; exact hk
  have hpfA : ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length
      < (listPairs s).length := Nat.mod_lt _ hpos
  have hpfB : ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length < s.length :=
    Nat.lt_of_lt_of_eq hpfA hlen
  have hpfC : ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length
      < (s.drop 1 ++ s.take 1).length :=
    Nat.lt_of_lt_of_eq hpfB (Eq.symm (rot1_length s))
  have hxy : (listPairs s)[(listPairs s).idxOf (x, y)] = (x, y) :=
    List.getElem_idxOf hk
  have hpair : (listPairs s)[(listPairs s).idxOf (x, y)]'(by
      show (listPairs s).idxOf (x, y) < (s.zip (s.drop 1 ++ s.take 1)).length
      rw [List.length_zip]; exact lt_min_iff.mpr ⟨hkL, by rw [rot1_length]; exact hkL⟩)
      = (s[(listPairs s).idxOf (x, y)]'hkL,
         (s.drop 1 ++ s.take 1)[(listPairs s).idxOf (x, y)]'(
          by rw [rot1_length]; exact hkL)) :=
    getElemListPairs hkL (by rw [rot1_length]; exact hkL)
  have hrot : (s.drop 1 ++ s.take 1)[(listPairs s).idxOf (x, y)]'(
      by rw [rot1_length]; exact hkL)
      = s[((listPairs s).idxOf (x, y) + 1) % s.length]'(Nat.mod_lt _ hposl) :=
    getElem_rot1' s (by rw [rot1_length]; exact hkL)
  have hy : s[((listPairs s).idxOf (x, y) + 1) % s.length]'(Nat.mod_lt _ hposl) = y :=
    hrot.symm.trans (congrArg Prod.snd (hpair.symm.trans hxy))
  have hmemY : y ∈ s := hy ▸ List.getElem_mem (Nat.mod_lt _ hposl)
  have hidxY : s.idxOf y = ((listPairs s).idxOf (x, y) + 1) % s.length := by
    have h9 := List.Nodup.idxOf_getElem hn
      (i := ((listPairs s).idxOf (x, y) + 1) % s.length) (Nat.mod_lt _ hposl)
    rw [hy] at h9
    exact h9
  have hnext : nextEl s y =
      s[(((listPairs s).idxOf (x, y) + 1) % s.length + 1) % s.length]'(
        Nat.mod_lt _ hposl) := by
    rw [TameLp.nextEl_eq_getD hmemY, hidxY, TameLp.getD_eq_getElem_of_lt (Nat.mod_lt _ hposl)]
  have hz : (listPairs s)[((listPairs s).idxOf (x, y) + 1) % (listPairs s).length]'hpfA
      = (s[((listPairs s).idxOf (x, y) + 1) % (listPairs s).length]'hpfB,
         (s.drop 1 ++ s.take 1)[((listPairs s).idxOf (x, y) + 1) % (listPairs s).length]'hpfC) :=
    getElemListPairs hpfB hpfC
  have hAB : ((listPairs s).idxOf (x, y) + 1) % (listPairs s).length
      = ((listPairs s).idxOf (x, y) + 1) % s.length := by rw [hlen]
  have hA : s[((listPairs s).idxOf (x, y) + 1) % (listPairs s).length]'hpfB = y :=
    (getElemConN67 hpfB (Nat.mod_lt _ hposl) hAB).symm ▸ hy
  have hCD0 : (((listPairs s).idxOf (x, y) + 1) % (listPairs s).length + 1) % s.length
      = (((listPairs s).idxOf (x, y) + 1) % s.length + 1) % s.length := by rw [hlen]
  have hB : (s.drop 1 ++ s.take 1)[((listPairs s).idxOf (x, y) + 1) % (listPairs s).length]'hpfC
      = s[(((listPairs s).idxOf (x, y) + 1) % s.length + 1) % s.length]'(
        Nat.mod_lt _ hposl) :=
    (getElem_rot1' s hpfC).trans
      (getElemConN67 (Nat.mod_lt _ hposl) (Nat.mod_lt _ hposl) hCD0)
  rw [TameLp.nextEl_eq_getD hp, TameLp.getD_eq_getElem_of_lt hpfA (x, y), hz, hA, hnext, hB]

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针已执行，快照 t67_axiom_audit.log 全文）：
本件公开件探针——bijOn 群（bijOn_rxESwap/bijOn_rxFList/bijOn_rxNList）、
hypermapOfListG、四槽（darts/edgeMap/nodeMap/faceMap_hypermapOfListG）、
缺口底座（darts_eq_iUnion_*、iterateMapValuation、pow_mod_eq、
face_eq_orbit_range、hypMapsInvs、prevEl_eq_getD_idxOf、
nextEl_eq_getElem、prevEl_eq_getD_idxOf、nextElListPairsG、
prevElListPairs、getElem_rot1'/getElemListPairs/getElemConN67/rot1_length）——
全件零 sorryAx（标准三内或其子集）。
#print axioms Kepler.Text.TameSpine.bijOn_rxNList
#print axioms Kepler.Text.TameSpine.hypermapOfListG
#print axioms Kepler.Text.TameSpine.nextElListPairsG
#print axioms Kepler.Text.TameSpine.prevElListPairs
#print axioms Kepler.Text.TameSpine.hypMapsInvs
#print axioms Kepler.Text.TameSpine.darts_eq_iUnion_faceSet
-/
