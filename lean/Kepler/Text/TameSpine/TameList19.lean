/-
  Kepler.Text.TameSpine.TameList19 — B1 Tame_list 地基批 19：iso 章 + 小工具箱
  /list_pairs 旋转章（tamespine-port-plan §4 批次表 B1 行；接续批 18 =
  TameList18.lean，批 18 终点 = HOL :10341（QRDYXYJ_list 已落，
  iso_list_restricted :10344 起留给本批）；本批起点 = HOL :10344）。

  本批镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353，
  text_formalization/tame/tame_list.hl:10344-:10554）——iso 章 1 枚 +
  小工具箱 9 枚 + list_pairs 旋转章 3 枚，共 13 枚全量：

  iso 章：`iso_list_restricted` :10344。
  小工具箱：`INJ_EMPTY` :10361 / `set_of_list_rev` :10369 / `el_iota` :10377 /
  `I_POWER` :10389 / `hd_iota` :10399 / `list_pairs_empty_alt` :10410 /
  `set_of_list_pairs_set_of_list_subset` :10418 /
  `set_of_list_pairs_set_of_list_eq` :10432 / `card_set_of_list_uniq2` :10442。
  旋转章：`list_pairs_rot` :10454 / `list_pairs_rot_subset` :10495 /
  `e_list_image` :10534。:10556 自然边界收批（`e_list_pairs_rev` 起留批 20）。

  层级侦察定论（本批新记档）：旋转章 HOL 泛型 `A` 在全部下游消费点
  （e_list_pairs_rev :10556 → AUQTZYZ_list，more_tame_concl.hl:403）取
  A = ℕ——f r 为面-顶点表 `List ℕ`，`list_pairs f` 的元为 dart `ℕ × ℕ`
  （批 16 listPairsGetElemT / 批 2 memListPairsIota 同层级先例），
  `e_list d` = dart 对换 `eList`（GoodListDefs.lean:59）。故旋转章与
  set_of_list 家族冻结在 List ℕ 层；`set_of_list` 双级载体：面元级 ↦
  本批新载体 `setOfListNatSpine`（批 11 同款折算，List ℕ 元）、
  `set_of_list (list_pairs f)` 的 dart 级 ↦ 批 11 `setOfListSpine`。

  依赖面（全为在案真件，零新增债）：批 1 `IsoListSpine`/`GNBEVVU`
  （Hypermap 层桥，tame_list.hl:3540——批 18 交接段侦察记档的 DAKEFCC/GNBEVVU
  双桥均已在案，无需新侦察件）+ 批 15 `isoRestrictedIff`（DAKEFCC =
  iso_restricted :9346/:9360 的 Lean 面，TameList1 §4 记档 + TameList15 §5
  落地）/ 批 11 `setOfListSpine` / TameLp `la7_length_listPairs`/
  `la7_getElem_rotOne`/`la7_length_rotOne`/`la7_mem_listPairs_reverse` / 批 2
  `rotateSpineOne`+`idxUniq` / 批 16 listPairsGetElemT 同证重推导（批 16 私件
  为私有不跨文件，本批 List ℕ 面重推导）/ 批 10 nextElStep/
  nextElIterateGetElem 的 List ℕ 面同证重推导 / Hypermap 层 `IsRestricted`
  （hypermap.hl:11174，Hypermap.lean:9645 在案）。

  载体折算（沿批 1-18 约定）：`rot k` ↦ `List.rotate k`（批 3 rotate 群同款，
  范围外 `next_el_power_rot` :5036 载体 = `Function.iterate` 轨道枚举 + Fin
  单射计长 + `List.getElem_rotate`，HOL 的 rot_eq_rot/next_el_power_eq 长链
  同构替代）；`POWER` ↦ `Function.iterate`；`iota j n` ↦ `List.range' j n`
  （批 2 range 面同族）；`I` ↦ `Function.id`；`HD` ↦ `head!`；`EL` ↦
  `getElem`；`indexl` ↦ `idxOf`；`uniq` ↦ `List.Nodup`；`sizel` ↦
  `List.length`（批 12 记账）。

  诚实记账：本批十三件全部真证，零新增记账债（零止损件）。
  iso_list_restricted 的 HOL 原文 `is_restricted (hypermap_of_list L)` 无
  good_list L 前提，Lean 侧 hypermapOfList 持 GoodList 证明参——按批 12
  Skolem 折算惯例以 `isoListSpine_goodList hiso hL'` 显式给出（Prop 层
  proof irrelevance，语义零收窄）。e_list_image 的 HOL 前提 `~(f = [])`
  在 Lean 面不被消费（list_pairs_rot_subset 对空表自洽），按批 18 `_hgn`
  惯例以 `_hne` 显式保留。公理审计实测（#print axioms，2026-10-13，隔离
  clone）：十三件均仅依赖标准三 [propext, Classical.choice, Quot.sound]
  （injEmpty/iPower/hdIota 零公理，elIota/listPairsEmptyAlt/
  setOfListSpineRev 仅 propext 面），零 sorryAx、零记账传入。

  红线遵守：本模块全部定理真证（零未证缺口桩）、零既有文件触碰、零 git
  写操作。批 20 接续点：HOL :10556 `e_list_pairs_rev`（`!f r. uniq f /\
  ~(f = []) /\ sizel f = sizel r /\ (!d. MEM d (list_pairs f) ==> MEM
  (e_list d) (list_pairs r)) /\ HD f = LAST r ==> r = rev f`，走本批
  eListImage + Seq.revK/rot_oversize/index_rot/index_hd0 链——`Seq.revK`
  （rev (rev x) = x）与 `Seq.rot_oversize` 的 rotate 侧折算、批 3
  indexfRot/indexfRotn 可资；:10584 COND_CASES 后半为 rotate 位移算术，
  需 Seq2.index_rot 全量形侦察）。
-/

import Kepler.Text.TameSpine.TameList18

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl eList listPairs GoodList)
open Kepler.Graphs (fgraph)
open Kepler.Text.TameLp (hypermapOfList nextEl_eq_getD getD_eq_getElem_of_lt
  getElem_idxOf idxOf_getElem nextEl_mem_of_mem la7_length_listPairs
  la7_getElem_rotOne la7_length_rotOne la7_mem_listPairs_reverse)

/-! ### §0 私件引擎（批 10/16 私件不跨文件，List ℕ 面同证重推导） -/

/-- getElem 下标换形（批 10 getElemCon 同证重推导）。 -/
private theorem getElemConD {s : List ℕ} {i j : ℕ} (hi : i < s.length)
    (hj : j < s.length) (h : i = j) : s[i]'hi = s[j]'hj := by
  subst h; rfl

/-- getElem 表换形（批 16 getElem_congr_list 同证重推导；rw 跨表等价的
motive 问题的免疫器）。 -/
private theorem getElemCongrListD {l₁ l₂ : List ℕ} (h : l₁ = l₂) {j : ℕ}
    (h₁ : j < l₁.length) (h₂ : j < l₂.length) : l₁[j]'h₁ = l₂[j]'h₂ := by
  subst h; rfl

/-- 单步轨道（批 10 nextElStep 同证重推导）：nodup 表第 `j` 项的
`next_el` = 第 `(j+1) mod len` 项。 -/
private theorem nextElStepD {s : List ℕ} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (hj1 : (j + 1) % s.length < s.length) :
    nextEl s (s[j]'hj) = s[(j + 1) % s.length]'hj1 := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  rw [nextEl_eq_getD (List.getElem_mem hj), idxOf_getElem hsn hj,
    getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

/-- 轨道枚举（批 10 nextElIterateGetElem 同证重推导；HOL `Seq2.next_el_power`
载体形）：nodup 表上 `next_el` 幂从第 `j` 项出发按 mod 下标走。 -/
private theorem nextElIterateGetElemD {s : List ℕ} (hsn : s.Nodup) {j : ℕ}
    (hj : j < s.length) (n : ℕ) (hjn : (j + n) % s.length < s.length) :
    (nextEl s)^[n] (s[j]'hj) = s[(j + n) % s.length]'hjn := by
  have hpos : 0 < s.length := List.length_pos_of_mem (List.getElem_mem hj)
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    exact getElemConD hj hjn (by rw [Nat.add_zero, Nat.mod_eq_of_lt hj])
  | succ k ih =>
    have hjk : (j + k) % s.length < s.length := Nat.mod_lt _ hpos
    rw [Function.iterate_succ_apply', ih hjk,
      nextElStepD hsn hjk (Nat.mod_lt ((j + k) % s.length + 1) hpos)]
    refine getElemConD (Nat.mod_lt _ hpos) hjn ?_
    have hmod : ((j + k) % s.length + 1) % s.length = (j + k + 1) % s.length :=
      Nat.mod_add_mod (j + k) s.length 1
    rw [hmod, Nat.add_assoc]

/-- `list_pairs l` 的逐项式（HOL `nth_list_pairs` 的 rot-1 位移，任意表成立；
批 16 listPairsGetElemT 同证重推导）。 -/
private theorem listPairsGetElemD {l : List ℕ} {j : ℕ} (hj : j < l.length)
    (hl : j < (listPairs l).length) (hm : (j + 1) % l.length < l.length) :
    (listPairs l)[j]'hl = (l[j]'hj, l[(j + 1) % l.length]'hm) := by
  have hpos : 0 < l.length := List.length_pos_of_mem (List.getElem_mem hj)
  have hrot' : (TameLp.la7RotOne l)[j]'(Nat.lt_of_lt_of_eq hj (la7_length_rotOne l).symm)
      = l[(j + 1) % l.length]'(Nat.mod_lt (j + 1) hpos) :=
    la7_getElem_rotOne hj
  have hid : TameLp.la7RotOne l = l.drop 1 ++ l.take 1 := by
    rw [show TameLp.la7RotOne l = l.rotate 1 from rfl, rotateSpineOne]
  have hhl' : j < (l.drop 1 ++ l.take 1).length := by
    rw [Eq.symm (rotateSpineOne l), List.length_rotate]
    exact hj
  have hcon : (l.drop 1 ++ l.take 1)[j]'hhl'
      = l[(j + 1) % l.length]'(Nat.mod_lt (j + 1) hpos) :=
    (getElemCongrListD hid (Nat.lt_of_lt_of_eq hj (la7_length_rotOne l).symm)
      hhl').symm.trans hrot'
  show (l.zip (l.drop 1 ++ l.take 1))[j]'hl = _
  rw [List.getElem_zip]
  show (l[j]'hj, (l.drop 1 ++ l.take 1)[j]'hhl')
      = (l[j]'hj, l[(j + 1) % l.length]'hm)
  rw [hcon]

/-- **HOL `mem_list_pairs_exists`**（ssreflect list_hypermap-compiled.hl:763
`MEM x l <=> ?y. MEM (x,y) (list_pairs l)`）的 iff
（批 16 listPairsMemExists 的 ∃-半同证重推导 + getElem 反向）。 -/
private theorem memListPairsExistsIff {l : List ℕ} {x : ℕ} :
    x ∈ l ↔ ∃ y, (x, y) ∈ listPairs l := by
  constructor
  · intro hx
    have hj : l.idxOf x < l.length := List.idxOf_lt_length_iff.mpr hx
    have hpos : 0 < l.length := List.length_pos_of_mem hx
    have hl' : l.idxOf x < (listPairs l).length := by
      rw [la7_length_listPairs]; exact hj
    have hget := listPairsGetElemD hj hl' (Nat.mod_lt _ hpos)
    refine ⟨nextEl l x, ?_⟩
    have heq : (x, nextEl l x) = (listPairs l)[l.idxOf x]'hl' := by
      rw [nextEl_eq_getD hx, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos), hget]
      exact congrArg₂ _ (getElem_idxOf hx).symm rfl
    rw [heq]
    exact List.getElem_mem hl'
  · rintro ⟨y, hy⟩
    obtain ⟨i, hi, hxy⟩ := List.mem_iff_getElem.mp hy
    have hlen : (listPairs l).length = l.length := la7_length_listPairs l
    have hil : i < l.length := by rw [← hlen]; exact hi
    have hpos : 0 < l.length := List.length_pos_of_mem (List.getElem_mem hil)
    have hgt := listPairsGetElemD hil hi (Nat.mod_lt _ hpos)
    rw [hgt] at hxy
    have hx : x = l[i]'hil := congrArg Prod.fst hxy.symm
    rw [hx]
    exact List.getElem_mem hil

/-- **HOL `mem_list_pairs_explicit`**（ssreflect list_hypermap-compiled.hl:295
`uniq s /\ MEM (x,y) (list_pairs s) ==> y = next_el s x`）。 -/
private theorem listPairsMemExplicit {l : List ℕ} (hnd : l.Nodup)
    {p q : ℕ} (h : (p, q) ∈ listPairs l) : q = nextEl l p := by
  obtain ⟨i, hi, hxy⟩ := List.mem_iff_getElem.mp h
  have hlen : (listPairs l).length = l.length := la7_length_listPairs l
  have hil : i < l.length := by rw [← hlen]; exact hi
  have hpos : 0 < l.length := List.length_pos_of_mem (List.getElem_mem hil)
  have hgt := listPairsGetElemD hil hi (Nat.mod_lt _ hpos)
  rw [hgt] at hxy
  have hp : p = l[i]'hil := congrArg Prod.fst hxy.symm
  have hq : q = l[(i + 1) % l.length]'(Nat.mod_lt _ hpos) :=
    congrArg Prod.snd hxy.symm
  have hpm : p ∈ l := hp.symm ▸ List.getElem_mem hil
  have hpidx : l.idxOf p = i :=
    (congrArg l.idxOf hp).trans (idxOf_getElem hnd hil)
  rw [hq, nextEl_eq_getD hpm, hpidx, getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

/-- **HOL `list_pairs_unique`**（tame_list.hl:4110-4113
`!f d1 d2. uniq f /\ MEM d1 (list_pairs f) /\ MEM d2 (list_pairs f) /\
FST d1 = FST d2 ==> d1 = d2`）（拆对版）。 -/
private theorem listPairsUniqueNat {l : List ℕ} (hnd : l.Nodup)
    {p q r : ℕ} (h1 : (p, q) ∈ listPairs l) (h2 : (p, r) ∈ listPairs l) :
    (p, q) = (p, r) := by
  rw [listPairsMemExplicit hnd h1, listPairsMemExplicit hnd h2]

/-- HOL `set_of_list` 的 ℕ（面-顶点元）级载体（批 11 `setOfListSpine` 的
List ℕ 同款折算；旋转章 u v 为面表 List ℕ——AUQTZYZ_list 消费面，
`set_of_list (list_pairs f)` 的 dart 级则走批 11 `setOfListSpine`）。 -/
def setOfListNatSpine (l : List ℕ) : Set ℕ := {x | x ∈ l}

/-- `setOfListNatSpine` 的 Finset 桥（批 18 cardAtomsOfLoop 内联同款）。 -/
private theorem setOfListNatSpineCoe (l : List ℕ) :
    (setOfListNatSpine l : Set ℕ) = (l.toFinset : Set ℕ) := by
  ext x
  constructor
  · intro hx; exact List.mem_toFinset.mpr hx
  · intro hx; exact List.mem_toFinset.mp hx

/-- 轨道计长内核：互异轨道点全落 `t` ⇒ 长度不超过（Fin-单射 + 卡片计数；
nextElPowerRotD 的内基于弹）。 -/
private theorem lengthLeOfInjectiveMem {t : List ℕ} {F : ℕ → ℕ}
    {n : ℕ} (_htn : t.Nodup)
    (hdist : ∀ i j : ℕ, i < n → j < n → F i = F j → i = j)
    (hmem : ∀ i : ℕ, i < n → F i ∈ t) : n ≤ t.length := by
  have hinj : Function.Injective
      (fun i : Fin n => (⟨t.idxOf (F i.val),
        List.idxOf_lt_length_iff.mpr (hmem i.val i.isLt)⟩ : Fin t.length)) := by
    intro i j hij
    have hio : t.idxOf (F i.val) = t.idxOf (F j.val) := congrArg Fin.val hij
    have hF : F i.val = F j.val :=
      idxUniq (hmem i.val i.isLt) (hmem j.val j.isLt) hio
    exact Fin.ext (hdist i.val j.val i.isLt j.isLt hF)
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa using hcard

/-- **HOL `next_el_power_rot`**（tame_list.hl:5036-5040，范围外载体，§0 私件
同证重推导）
`!s t d. uniq s /\ uniq t /\ MEM d s /\ MEM d t /\
  (!i. (next_el s POWER i) d = (next_el t POWER i) d) ==> ?k. rot k s = t`。
证明改道：HOL 走 rot_eq_rot/next_el_power_eq/rot_to_index 长链，此处以
轨道枚举（nextElIterateGetElemD）+ Fin-单射计长（lengthLeOfInjectiveMem）+
`List.getElem_rotate` 直接构造，语义同构。 -/
private theorem nextElPowerRotD {u v : List ℕ} (hu : u.Nodup)
    (hv : v.Nodup) {d : ℕ} (hdu : d ∈ u) (hdv : d ∈ v)
    (hit : ∀ i, (nextEl u)^[i] d = (nextEl v)^[i] d) : ∃ k, u.rotate k = v := by
  have hu0 : 0 < u.length := List.length_pos_of_mem hdu
  have hv0 : 0 < v.length := List.length_pos_of_mem hdv
  set k := u.idxOf d with hkdef
  set k' := v.idxOf d with hk'def
  have hkl : k < u.length := List.idxOf_lt_length_iff.mpr hdu
  have hk'l : k' < v.length := List.idxOf_lt_length_iff.mpr hdv
  have hdU : d = u[k]'hkl := (getElem_idxOf hdu).symm
  have hdV : d = v[k']'hk'l := (getElem_idxOf hdv).symm
  -- 轨道式（隐式 q 供 rw 证明参匹配）
  have orbitU : ∀ (i : ℕ) {q : (k + i) % u.length < u.length},
      (nextEl u)^[i] d = u[(k + i) % u.length]'q := fun i q =>
    hdU ▸ nextElIterateGetElemD hu hkl i (Nat.mod_lt _ hu0)
  have orbitV : ∀ (i : ℕ) {q : (k' + i) % v.length < v.length},
      (nextEl v)^[i] d = v[(k' + i) % v.length]'q := fun i q =>
    hdV ▸ nextElIterateGetElemD hv hk'l i (Nat.mod_lt _ hv0)
  -- 轨道点保持在表内
  have iterMemU : ∀ i : ℕ, (nextEl u)^[i] d ∈ u := by
    intro i
    induction i with
    | zero => simpa using hdu
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact nextEl_mem_of_mem ih
  have iterMemV : ∀ i : ℕ, (nextEl v)^[i] d ∈ v := by
    intro i
    induction i with
    | zero => simpa using hdv
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact nextEl_mem_of_mem ih
  -- getElem 下标单射
  have getIdxInjU : ∀ (i j : ℕ) (hi : i < u.length) (hj : j < u.length),
      u[i]'hi = u[j]'hj → i = j := by
    intro i j hi hj hcon
    have h1 : u.idxOf (u[i]'hi) = i := idxOf_getElem hu hi
    rw [hcon] at h1
    exact h1.symm.trans (idxOf_getElem hu hj)
  have getIdxInjV : ∀ (i j : ℕ) (hi : i < v.length) (hj : j < v.length),
      v[i]'hi = v[j]'hj → i = j := by
    intro i j hi hj hcon
    have h1 : v.idxOf (v[i]'hi) = i := idxOf_getElem hv hi
    rw [hcon] at h1
    exact h1.symm.trans (idxOf_getElem hv hj)
  -- 轨道互异
  have distU : ∀ i j : ℕ, i < u.length → j < u.length →
      (nextEl u)^[i] d = (nextEl u)^[j] d → i = j := by
    intro i j hi hj hF
    have e1 : u[(k + i) % u.length]'(Nat.mod_lt _ hu0)
        = u[(k + j) % u.length]'(Nat.mod_lt _ hu0) := by
      rw [← orbitU i, ← orbitU j]; exact hF
    have himod := getIdxInjU _ _ (Nat.mod_lt _ hu0) (Nat.mod_lt _ hu0) e1
    have hmeq' : i % u.length = j % u.length :=
      Nat.ModEq.add_left_cancel' k himod
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmeq'
  have distV : ∀ i j : ℕ, i < v.length → j < v.length →
      (nextEl v)^[i] d = (nextEl v)^[j] d → i = j := by
    intro i j hi hj hF
    have e1 : v[(k' + i) % v.length]'(Nat.mod_lt _ hv0)
        = v[(k' + j) % v.length]'(Nat.mod_lt _ hv0) := by
      rw [← orbitV i, ← orbitV j]; exact hF
    have himod := getIdxInjV _ _ (Nat.mod_lt _ hv0) (Nat.mod_lt _ hv0) e1
    have hmeq' : i % v.length = j % v.length :=
      Nat.ModEq.add_left_cancel' k' himod
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmeq'
  -- 双向计长
  have hle1 : u.length ≤ v.length :=
    lengthLeOfInjectiveMem (t := v) hv (F := fun i => (nextEl u)^[i] d)
      (n := u.length) distU (fun i _ => by rw [hit i]; exact iterMemV i)
  have hle2 : v.length ≤ u.length :=
    lengthLeOfInjectiveMem (t := u) hu (F := fun i => (nextEl v)^[i] d)
      (n := v.length) distV (fun i _ => by rw [← hit i]; exact iterMemU i)
  have hlv : u.length = v.length := Nat.le_antisymm hle1 hle2
  -- 两侧各把 d 转到首位后逐项相等
  have hrot : u.rotate k = v.rotate k' := by
    refine List.ext_get ?_ (fun j h1 h2 => ?_)
    · rw [List.length_rotate, List.length_rotate]; exact hlv
    · show (u.rotate k)[j]'h1 = (v.rotate k')[j]'h2
      rw [List.getElem_rotate, List.getElem_rotate]
      rw [Nat.add_comm j k, Nat.add_comm j k']
      rw [← orbitU j, ← orbitV j]
      exact hit j
  refine ⟨k + (v.length - k'), ?_⟩
  have hkv : k' + (v.length - k') = v.length := Nat.add_sub_cancel' hk'l.le
  calc u.rotate (k + (v.length - k'))
      = (u.rotate k).rotate (v.length - k') :=
        (List.rotate_rotate u k (v.length - k')).symm
    _ = (v.rotate k').rotate (v.length - k') := by rw [hrot]
    _ = v.rotate (k' + (v.length - k')) := List.rotate_rotate v k' _
    _ = v.rotate v.length := by rw [hkv]
    _ = v := List.rotate_length v

/-! ### §1 iso 章（tame_list.hl:10344-10357） -/

/-- **HOL `iso_list_restricted`**（tame_list.hl:10344-10347）
`!L L'. good_list L' /\
   iso_list (L',[]) (L,[]) /\ is_restricted (hypermap_of_list L) ==>
  is_restricted (hypermap_of_list L')`
——DAKEFCC（= `iso_restricted` :9346/:9360，Lean 面 = 批 15
`isoRestrictedIff`）+ GNBEVVU（批 1，tame_list.hl:3540 Hypermap 层桥）：
HOL 的 `INTRO_TAC DAKEFCC [hypermap_of_list L'; hypermap_of_list L]` 即
`GNBEVVU hL' hiso` 的 Iso 方向，is_restricted 支由 isoRestrictedIff 的
mpr 收口。`is_restricted (hypermap_of_list L)` 的 Lean 面 hypermapOfList
持 GoodList 证明参——按批 12 Skolem 折算惯例取
`isoListSpine_goodList hiso hL'`（Prop 层 proof irrelevance，零收窄）。 -/
theorem isoListRestricted {L L' : fgraph ℕ} (hL' : GoodList L')
    (hiso : IsoListSpine L' L [] [])
    (hr : (hypermapOfList L (isoListSpine_goodList hiso hL')).IsRestricted) :
    (hypermapOfList L' hL').IsRestricted :=
  (isoRestrictedIff (GNBEVVU hL' hiso)).mp hr

/-! ### §2 小工具箱（tame_list.hl:10361-10452） -/

/-- **HOL `INJ_EMPTY`**（tame_list.hl:10361-10362）`!f:A->B Y. INJ f {} Y`
——本仓 Mathlib 的 `Set.InjOn (f) (s)` 为单参谓词（目标集 Y 不入参），
按现签名折算（INJ f s Y 的 Y 仅约束值域类型，零收窄）。 -/
theorem injEmpty {α β : Type*} {f : α → β} :
    Set.InjOn f (∅ : Set α) := by
  intro x hx y _ _
  exact absurd hx (Set.notMem_empty x)

/-- **HOL `set_of_list_rev`**（tame_list.hl:10369-10370）
`!u. set_of_list (rev u) = set_of_list u`（面元级载体）。 -/
theorem setOfListSpineRev (u : List ℕ) :
    setOfListNatSpine u.reverse = setOfListNatSpine u := by
  ext x
  exact List.mem_reverse

/-- **HOL `el_iota`**（tame_list.hl:10377-10378）
`!j n i. i < n ==> EL i (iota j n) = j+i`（`iota j n` ↦ `List.range' j n`）。 -/
theorem elIota {j n i : ℕ} (h : i < n) :
    (List.range' j n)[i]'(by rw [List.length_range']; exact h) = j + i :=
  List.getElem_range'_1 i (by rw [List.length_range']; exact h)

/-- **HOL `I_POWER`**（tame_list.hl:10389-10390）`!n. I POWER n = I`。 -/
theorem iPower {α : Type*} (n : ℕ) : (id : α → α)^[n] = id :=
  Function.iterate_id n

/-- **HOL `hd_iota`**（tame_list.hl:10399-10400）
`!n a. ~(n=0) ==> HD (iota a n) = a`。 -/
theorem hdIota {n a : ℕ} (h : n ≠ 0) : (List.range' a n).head! = a := by
  rcases n with _ | m
  · exact absurd rfl h
  · rw [List.range'_succ]
    rfl

/-- **HOL `list_pairs_empty_alt`**（tame_list.hl:10410-10411）
`list_pairs [] = []`。 -/
theorem listPairsEmptyAlt : listPairs ([] : List ℕ) = [] := by
  simp [listPairs]

/-- **HOL `set_of_list_pairs_set_of_list_subset`**（tame_list.hl:10418-10421）
`!u v. set_of_list (list_pairs u) SUBSET set_of_list (list_pairs v) ==>
  set_of_list u SUBSET set_of_list v`（pairs 层走批 11 `setOfListSpine`，
面元层走 `setOfListNatSpine`；mem_list_pairs_exists 两向）。 -/
theorem setOfListPairsSetOfListSubset {u v : List ℕ}
    (h : setOfListSpine (listPairs u) ⊆ setOfListSpine (listPairs v)) :
    setOfListNatSpine u ⊆ setOfListNatSpine v := by
  intro x hx
  obtain ⟨y, hy⟩ := memListPairsExistsIff.mp hx
  exact memListPairsExistsIff.mpr ⟨y, h hy⟩

/-- **HOL `set_of_list_pairs_set_of_list_eq`**（tame_list.hl:10432-10435）
`!u v. set_of_list (list_pairs u) = set_of_list (list_pairs v) ==>
  set_of_list u = set_of_list v`（subset 版两向 + antisymm，与 HOL
SUBSET_ANTISYM_EQ 同构）。 -/
theorem setOfListPairsSetOfListEq {u v : List ℕ}
    (h : setOfListSpine (listPairs u) = setOfListSpine (listPairs v)) :
    setOfListNatSpine u = setOfListNatSpine v :=
  Set.Subset.antisymm (setOfListPairsSetOfListSubset (le_of_eq h))
    (setOfListPairsSetOfListSubset (le_of_eq h.symm))

/-- **HOL `card_set_of_list_uniq2`**（tame_list.hl:10442-10443）
`!l. CARD (set_of_list l) = sizel l ==> uniq l`（逆向经 Multiset 的
toFinset-card-iff-nodup，与 HOL ltn_size_undup/undup_uniq 链同构）。 -/
theorem cardSetOfListUniq2 {l : List ℕ}
    (h : (setOfListNatSpine l).ncard = l.length) : l.Nodup := by
  have hco : (setOfListNatSpine l).ncard = l.toFinset.card := by
    rw [setOfListNatSpineCoe]; exact Set.ncard_coe_finset _
  rw [hco] at h
  refine (Multiset.toFinset_card_eq_card_iff_nodup (m := (l : Multiset ℕ))).mp ?_
  exact h

/-! ### §3 list_pairs 旋转章（tame_list.hl:10454-10554） -/

/-- **HOL `list_pairs_rot`**（tame_list.hl:10454-10457）
`!u v. uniq u /\ sizel u = sizel v /\
  set_of_list (list_pairs u) = set_of_list (list_pairs v) ==> (?k. rot k u = v)`
——空情形直接收口；非空走 HOL 同构：set_of_list_pairs_set_of_list_eq +
card_set_of_list_uniq 桥 + card_set_of_list_uniq2 升 uniq v，头元入 v，再按
next_el 幂归纳（mem_list_pairs_exists + mem_list_pairs_explicit 两桥）得全
轨道相等，末经 next_el_power_rot（nextElPowerRotD）收口。 -/
theorem listPairsRot {u v : List ℕ} (hu : u.Nodup)
    (hlen : u.length = v.length)
    (h : setOfListSpine (listPairs u) = setOfListSpine (listPairs v)) :
    ∃ k, u.rotate k = v := by
  rcases u with _ | ⟨a, t⟩
  · rcases v with _ | ⟨b, s⟩
    · exact ⟨0, rfl⟩
    · simp at hlen
  · have hu0 : (a :: t) ≠ [] := by simp
    -- uniq v（卡片链：CARD (set_of_list v) = CARD (set_of_list u) = sizel u = sizel v）
    have hA : setOfListNatSpine (a :: t) = setOfListNatSpine v :=
      setOfListPairsSetOfListEq h
    have hvu : v.Nodup := by
      refine cardSetOfListUniq2 ?_
      rw [← hA, setOfListNatSpineCoe, Set.ncard_coe_finset,
        List.toFinset_card_of_nodup hu, hlen]
    -- 轨道逐步相等（HOL ENOUGH_TO_SHOW 的强化归纳）
    have iterMemU : ∀ (m : ℕ) (d : ℕ), d ∈ a :: t →
        (nextEl (a :: t))^[m] d ∈ a :: t := by
      intro m d hd
      induction m with
      | zero => simpa using hd
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact nextEl_mem_of_mem ih
    have hitAll : ∀ (i : ℕ) (d : ℕ), d ∈ a :: t → d ∈ v →
        (nextEl (a :: t))^[i] d = (nextEl v)^[i] d := by
      intro i
      induction i with
      | zero => intro d _ _; rfl
      | succ m ih =>
        intro d hdu hdv
        have hXY : (nextEl (a :: t))^[m] d = (nextEl v)^[m] d := ih d hdu hdv
        have hmemXU : (nextEl (a :: t))^[m] d ∈ a :: t := iterMemU m d hdu
        obtain ⟨y, hpair⟩ := memListPairsExistsIff.mp hmemXU
        have hy1 : y = nextEl (a :: t) ((nextEl (a :: t))^[m] d) :=
          listPairsMemExplicit hu hpair
        have hpairV : ((nextEl (a :: t))^[m] d, y) ∈ listPairs v := by
          show ((nextEl (a :: t))^[m] d, y) ∈ setOfListSpine (listPairs v)
          rw [← h]; exact hpair
        have hy2 : y = nextEl v ((nextEl (a :: t))^[m] d) :=
          listPairsMemExplicit hvu hpairV
        have hstep : nextEl (a :: t) ((nextEl (a :: t))^[m] d)
            = nextEl v ((nextEl (a :: t))^[m] d) := hy1.symm.trans hy2
        rw [hXY] at hstep
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hXY]
        exact hstep
    -- 头元两侧在表中
    have hmemHdU : (a :: t).head! ∈ a :: t := List.head!_mem_self hu0
    have hmemHdV : (a :: t).head! ∈ v := by
      show (a :: t).head! ∈ setOfListNatSpine v
      rw [← hA]; exact hmemHdU
    exact nextElPowerRotD hu hvu hmemHdU hmemHdV
      (fun i => hitAll i (a :: t).head! hmemHdU hmemHdV)

/-- **HOL `list_pairs_rot_subset`**（tame_list.hl:10495-10498）
`!u v. uniq u /\ sizel u = sizel v /\
  set_of_list (list_pairs u) SUBSET set_of_list (list_pairs v) ==>
  (?k. rot k u = v)`
——HOL 同构：subset 升 set_of_list 单向，卡片链
（card_set_of_list_uniq = |u|、CARD_SET_OF_LIST_LE、CARD_SUBSET_LE）逼出
uniq v 与 set_of_list u = set_of_list v，再逐对 mem_list_pairs_exists +
list_pairs_unique 反逼 pairs 反向 subset，末 list_pairs_rot 收口。 -/
theorem listPairsRotSubset {u v : List ℕ} (hu : u.Nodup)
    (hlen : u.length = v.length)
    (h : setOfListSpine (listPairs u) ⊆ setOfListSpine (listPairs v)) :
    ∃ k, u.rotate k = v := by
  have h1 : setOfListNatSpine u ⊆ setOfListNatSpine v :=
    setOfListPairsSetOfListSubset h
  have hfin : (setOfListNatSpine v).Finite := by
    rw [setOfListNatSpineCoe]; exact Finset.finite_toSet _
  have hf : u.toFinset ≤ v.toFinset := fun x hx =>
    List.mem_toFinset.mpr (h1 (List.mem_toFinset.mp hx))
  have hnc : u.toFinset.card ≤ v.toFinset.card := Finset.card_le_card hf
  have cU : u.toFinset.card = u.length := List.toFinset_card_of_nodup hu
  have cVle : v.toFinset.card ≤ v.length := List.toFinset_card_le (l := v)
  have cVe : v.toFinset.card = v.length := by omega
  have hvu : v.Nodup := cardSetOfListUniq2 (by
    rw [setOfListNatSpineCoe, Set.ncard_coe_finset]; exact cVe)
  have hEqSets : setOfListNatSpine u = setOfListNatSpine v := by
    refine Set.eq_of_subset_of_ncard_le h1 ?_ hfin
    rw [setOfListNatSpineCoe u, setOfListNatSpineCoe v, Set.ncard_coe_finset,
      Set.ncard_coe_finset]
    omega
  have hrev : setOfListSpine (listPairs v) ⊆ setOfListSpine (listPairs u) := by
    intro d hd
    obtain ⟨p, q, hde⟩ : ∃ p q : ℕ, d = (p, q) := ⟨d.1, d.2, rfl⟩
    rw [hde] at hd ⊢
    have hpv : p ∈ v := memListPairsExistsIff.mpr ⟨q, hd⟩
    have hpu : p ∈ u := by
      show p ∈ setOfListNatSpine u
      rw [hEqSets]; exact hpv
    obtain ⟨q', hq'⟩ := memListPairsExistsIff.mp hpu
    have hInV : (p, q') ∈ listPairs v := h hq'
    have hEq := listPairsUniqueNat hvu hd hInV
    rw [hEq]
    exact hq'
  exact listPairsRot hu hlen (Set.Subset.antisymm h hrev)

/-- **HOL `e_list_image`**（tame_list.hl:10534-10538）
`!f r. uniq f /\ ~(f = []) /\ sizel f = sizel r /\
  (!d. MEM d (list_pairs f) ==> MEM (e_list d) (list_pairs r)) ==>
  (?k. rot k f = rev r)`
——list_pairs_rot_subset + list_pairs_rev_eq（TameLp
`la7_mem_listPairs_reverse`）+ e_list 对合（eList d 的逆像即 d 自身）；
HOL 的 Seq.size_rev 支 = `List.length_reverse`。`~(f = [])` 前提在
list_pairs_rot_subset 路线中不被消费，按批 18 `_hgn` 惯例以 `_hne`
显式保留（零收窄）。 -/
theorem eListImage {f r : List ℕ} (hu : f.Nodup) (_hne : f ≠ [])
    (hlen : f.length = r.length)
    (h : ∀ d ∈ listPairs f, eList d ∈ listPairs r) :
    ∃ k, f.rotate k = r.reverse := by
  have hsub : setOfListSpine (listPairs f)
      ⊆ setOfListSpine (listPairs r.reverse) := by
    intro d hd
    exact TameLp.la7_mem_listPairs_reverse.mpr (h d hd)
  exact listPairsRotSubset hu (by rw [List.length_reverse]; exact hlen) hsub

end Kepler.Text.TameSpine
