/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12B — AQ12 叶 W1b（decls 1–8）。

  HOL 锚：reference/flyspeck/text_formalization/tame/AQ12.hl:160-:408（249 HOL 行）
  ┌──────────────────────────────────────────────────────────────┐
  │ decl 1 `LAST_parts`        :160（14）                          │
  │ decl 2 `indexf_map`        :174（13）                          │
  │ decl 3 `mem_map_betwn`     :187（38）                          │
  │ decl 4 `last_map_betwn`    :225（32）                          │
  │ decl 5 `hd_map_betwn`      :257（28）                          │
  │ decl 6 `next_el_map_betwn` :285（66）                          │
  │ decl 7 `map_betwn`         :351（33）——**已在库 `mapBetwn`**，本批不重落 │
  │ decl 8 `FST_HD_MAP_betwn`  :384（25）                          │
  └──────────────────────────────────────────────────────────────┘

  ┌─ 路线勘误（相对清单的估工，重要）──────────────────────────────
  │ HOL 里 `map_betwn` 是**最后**证的（用 mem/last/hd/next_el 四件 +
  │ `eq_last_next` 装配）；本树 `mapBetwn`（JcajyduBetwnMap:72）已经
  │ 用 `betwnTakeDrop` 独立证出，且**比 HOL 的结论更强/等价**。
  │ 因此 decls 3–6 在本树是 `mapBetwn` 的**一行推论**（列表相等 ⇒
  │ 成员/LAST/HD/next_el 同值），不需要 `indexl_map`/`next_el_MEM_map`/
  │ `LAST_MAP`/`HD_MAP`/`HD_BETWN2` 的移植。故 W1b 的实际新内容 =
  │ decl 1 + decl 2（+ `aqs_idxOfMap`）+ decl 8。清单估 249 HOL →
  │ 实测约 1/3；这是「先扫已落批」的又一次兑现。
  └──────────────────────────────────────────────────────────────┘

  ┌─ 命名（编排者纪律）──────────────────────────────────────────
  │ 中立前缀 `aqs_`。其中两件被 AQ13/J2 下游消费（HOL 全树扫描）：
  │ · `LAST_parts` → **AQ13.hl**
  │ · `FST_HD_MAP_betwn` → **betwn_core0_z_y / betwn_corek_z_x / more_lemma1**
  │ （`map_betwn` 同三处下游消费，但已在库且名为公开 `mapBetwn`。）
  └──────────────────────────────────────────────────────────────┘

  载体折算：`LAST`/`HD` ↦ `List.getLast!`/`List.head!`（HOL 的 total 版；
  本批两件的实际输入均非空或 junk 分支恒等）；`parts L s` ↦ `partsSpine L s`；
  `MAP f` ↦ `List.map f`；`FST` ↦ `Prod.fst`。
  泛型实例沿 TameLp/TameList3 约定：`[BEq α] [LawfulBEq α] [DecidableEq α]`。

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList6
import Kepler.Text.TameSpine.TameList9
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.JcajyduBetwnMap

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl GoodList)
open Kepler.Graphs (fgraph between)

/-! ## §0 `Aq7`/`tame_list.indexl_map` 的 Lean 形：map 保 `idxOf` -/

/-- **HOL `Tame_list.indexl_map`**（tame_list.hl:988）：
`uniq s ∧ (∀ u v ∈ s, f u = f v → u = v) ∧ MEM y s ⇒
indexl (f y) (MAP f s) = indexl y s`（`indexl` ↦ `List.idxOf`）。 -/
theorem aqs_idxOfMap {α β : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β]
    {s : List α} {f : α → β} (hnd : s.Nodup)
    (hinj : ∀ u ∈ s, ∀ v ∈ s, f u = f v → u = v)
    {y : α} (hy : y ∈ s) : (s.map f).idxOf (f y) = s.idxOf y := by
  have hmap : (s.map f).Nodup := (List.nodup_map_iff_inj_on hnd).mpr hinj
  have hi : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hlt : s.idxOf y < (s.map f).length := by rwa [List.length_map]
  have h := Kepler.Text.TameLp.idxOf_getElem (s := s.map f) (i := s.idxOf y) hmap hlt
  rw [show (s.map f)[s.idxOf y]'hlt = f y from by
    rw [List.getElem_map, Kepler.Text.TameLp.getElem_idxOf hy]] at h
  exact h

/-! ## §1 AQ12.hl:174 `indexf_map` -/

/-- **HOL `indexf_map`**（AQ12.hl:174-:186）：单射映射保 `indexf`。
（HOL 走 `indexf_cond` + `indexl_map` + `size_map`；Lean 同路线，
`indexl_map` 用本批 §0 的 `aqs_idxOfMap`。） -/
theorem aqs_indexfMap {α β : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β]
    {s : List α} {f : α → β} (hnd : s.Nodup)
    (hinj : ∀ u ∈ s, ∀ v ∈ s, f u = f v → u = v)
    {y z : α} (hy : y ∈ s) (hz : z ∈ s) :
    indexf (f y) (f z) (s.map f) = indexf y z s := by
  have hmy : f y ∈ s.map f := List.mem_map_of_mem hy
  have hmz : f z ∈ s.map f := List.mem_map_of_mem hz
  rw [indexfCond hmy hmz, indexfCond hy hz, aqs_idxOfMap hnd hinj hy,
    aqs_idxOfMap hnd hinj hz, List.length_map]

/-! ## §2 AQ12.hl:160 `LAST_parts`（AQ13 消费，`aqs_` 中立名） -/

/-- **HOL `LAST_parts`**（AQ12.hl:160-:173）：
`normal_list L N ∧ MEM s N ∧ parts L s = sp ⇒ LAST (LAST sp) = LAST s`。
HOL 走 `normal_list_uniq_nonnil` + `parts_nonnil` + `parts_uniq_nonnil`
+ `parts_flatten` + `LAST_FLATTEN_2`（= 在库 `lastFlatten2`）；Lean 同路线
（`LAST` ↦ `getLast!`，非空支经 `getLast!EqGetLast` 折算）。 -/
theorem aqs_lastParts (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {s : List (ℕ × ℕ)}
    (hn : NormalListSpine hL N) (hs : s ∈ N)
    {sp : List (List (ℕ × ℕ))} (hsp : partsSpine L s = sp) :
    sp.getLast!.getLast! = s.getLast! := by
  subst hsp
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hs
  have hne : partsSpine L s ≠ [] := partsNonnil L hr1 hr2
  have hLne : (partsSpine L s).getLast hne ≠ [] :=
    (partsUniqNonnil L hL hn hs (List.getLast_mem hne)).2.2.2.1
  have hflat : (partsSpine L s).flatten ≠ [] := by
    rw [partsFlatten L hr1 hr2]
    exact hr2
  have key := lastFlatten2 hne hLne hflat
  -- `s.getLast hr2 = (partsSpine L s).flatten.getLast hflat`（经 getLast? 绕开依赖证明）
  have hgl : (partsSpine L s).flatten.getLast hflat = s.getLast hr2 := by
    have e : (partsSpine L s).flatten.getLast? = s.getLast? := by
      rw [partsFlatten L hr1 hr2]
    rw [List.getLast?_eq_some_getLast hr2, List.getLast?_eq_some_getLast hflat] at e
    exact Option.some.inj e
  rw [getLast!EqGetLast hne, getLast!EqGetLast hLne, getLast!EqGetLast hr2]
  exact key.symm.trans hgl

/-! ## §3 AQ12.hl:187-:350 `*_map_betwn` 四件（`mapBetwn` 的一行推论）

HOL 的证明顺序是先 mem/last/hd/next_el 四件、再用 `eq_last_next` 装配
`map_betwn`；本树 `mapBetwn`（JcajyduBetwnMap:72，`betwnTakeDrop` 路线）
已直接给出**列表相等**，故四件均为 `rw [mapBetwn]` 级推论，零重落。 -/

/-- **HOL `mem_map_betwn`**（AQ12.hl:187-:224）：`MAP f (betwn s y z)` 与
`betwn (MAP f s) (f y) (f z)` 同成员（`∀ x` 提升为参数）。 -/
theorem aqs_memMapBetwn {α β : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β]
    {s : List α} {f : α → β} (hnd : s.Nodup)
    (hinj : ∀ u ∈ s, ∀ v ∈ s, f u = f v → u = v)
    {y z : α} (hy : y ∈ s) (hz : z ∈ s) (hyz : y ≠ z) (x : β) :
    x ∈ (between s y z).map f ↔ x ∈ between (s.map f) (f y) (f z) := by
  rw [mapBetwn hnd hinj hy hz hyz]

/-- **HOL `last_map_betwn`**（AQ12.hl:225-:256）：两端 `LAST` 同值。 -/
theorem aqs_lastMapBetwn {α β : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β] [Inhabited β]
    {s : List α} {f : α → β} (hnd : s.Nodup)
    (hinj : ∀ u ∈ s, ∀ v ∈ s, f u = f v → u = v)
    {y z : α} (hy : y ∈ s) (hz : z ∈ s) (hyz : y ≠ z) :
    ((between s y z).map f).getLast! = (between (s.map f) (f y) (f z)).getLast! := by
  rw [mapBetwn hnd hinj hy hz hyz]

/-- **HOL `hd_map_betwn`**（AQ12.hl:257-:284）：两端 `HD` 同值。 -/
theorem aqs_hdMapBetwn {α β : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β] [Inhabited β]
    {s : List α} {f : α → β} (hnd : s.Nodup)
    (hinj : ∀ u ∈ s, ∀ v ∈ s, f u = f v → u = v)
    {y z : α} (hy : y ∈ s) (hz : z ∈ s) (hyz : y ≠ z) :
    ((between s y z).map f).head! = (between (s.map f) (f y) (f z)).head! := by
  rw [mapBetwn hnd hinj hy hz hyz]

/-- **HOL `next_el_map_betwn`**（AQ12.hl:285-:350）：段内逐点 `next_el` 同值。 -/
theorem aqs_nextElMapBetwn {α β : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    [BEq β] [LawfulBEq β] [DecidableEq β]
    {s : List α} {f : α → β} (hnd : s.Nodup)
    (hinj : ∀ u ∈ s, ∀ v ∈ s, f u = f v → u = v)
    {y z : α} (hy : y ∈ s) (hz : z ∈ s) (hyz : y ≠ z)
    (x : β) (_hx : x ∈ (between s y z).map f) :
    nextEl ((between s y z).map f) x = nextEl (between (s.map f) (f y) (f z)) x := by
  rw [mapBetwn hnd hinj hy hz hyz]

/-! ## §4 AQ12.hl:384 `FST_HD_MAP_betwn`（J2 下游消费，`aqs_` 中立名） -/

/-- **HOL `FST_HD_MAP_betwn`**（AQ12.hl:384-:408）：在 `parts L s` 的 parts 表上，
`FST ∘ HD` 把 `betwn sp py pz` 映到 `betwn (MAP (FST∘HD) sp) (FST y) (FST z)`。
HOL 走 `parts_uniq_nonnil`（py/pz 非空）+ `uniq_parts` + `uniq_imp_inj`
+ `parts_fst`（`HD py = y`、`HD pz = z`）+ `map_betwn`。 -/
theorem aqs_fstHdMapBetwn (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List (ℕ × ℕ))} {s : List (ℕ × ℕ)}
    (hn : NormalListSpine hL N) (hs : s ∈ N)
    {sp : List (List (ℕ × ℕ))} (hsp : partsSpine L s = sp)
    (huniq : (sp.map (fun p => p.head!.1)).Nodup)
    {py pz : List (ℕ × ℕ)} (hpy : py ∈ sp) (hpz : pz ∈ sp)
    {y z : ℕ × ℕ} (hy : y ∈ py) (hz : z ∈ pz) (hyz : y.1 ≠ z.1) :
    (between sp py pz).map (fun p => p.head!.1)
      = between (sp.map (fun p => p.head!.1)) y.1 z.1 := by
  subst hsp
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hs
  have hspnd : (partsSpine L s).Nodup := uniqParts L hr1 hr2
  have hpyne : py ≠ [] := (partsUniqNonnil L hL hn hs hpy).2.2.2.1
  have hpzne : pz ≠ [] := (partsUniqNonnil L hL hn hs hpz).2.2.2.1
  have hfpy : py.head!.1 = y.1 := (partsFst L hL hn hs hpy hy).symm
  have hfpz : pz.head!.1 = z.1 := (partsFst L hL hn hs hpz hz).symm
  have hpynz : py ≠ pz := by
    intro h
    apply hyz
    calc y.1 = py.head!.1 := partsFst L hL hn hs hpy hy
      _ = pz.head!.1 := by rw [h]
      _ = z.1 := (partsFst L hL hn hs hpz hz).symm
  have hmain := mapBetwn (s := partsSpine L s) (f := fun p => p.head!.1)
    hspnd (fun u hu v hv heq => uniqImpInj huniq hu hv heq) hpy hpz hpynz
  rw [hmain, hfpy, hfpz]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx——本件零消费 TameList16:1109 债链。） -/
#print axioms Kepler.Text.TameSpine.aqs_idxOfMap
#print axioms Kepler.Text.TameSpine.aqs_indexfMap
#print axioms Kepler.Text.TameSpine.aqs_lastParts
#print axioms Kepler.Text.TameSpine.aqs_memMapBetwn
#print axioms Kepler.Text.TameSpine.aqs_lastMapBetwn
#print axioms Kepler.Text.TameSpine.aqs_hdMapBetwn
#print axioms Kepler.Text.TameSpine.aqs_nextElMapBetwn
#print axioms Kepler.Text.TameSpine.aqs_fstHdMapBetwn
