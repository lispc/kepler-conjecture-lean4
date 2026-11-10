/-
  Kepler.Text.Reduction5Ml1Leaves — J5-2 K2 门控（主机 8b）前置叶件（ml1 波 1）。

  ┌─ 归属对账（HOL Light Flyspeck More_lemma1.hl）────────────────────
  │ :1147 `betwn_cat0`（15L）→ `betwnCat0`：
  │   uniq (cat s g) ∧ y,z ∈ s ∧ indexf y z s ≤ indexf y (LAST s) s ∧ y≠z
  │   ⇒ betwn (cat s g) y z = betwn s y z
  │ :471  `parts_betwn`（119L）→ 树内已完成（TameSpine/Reduction3CoreSplitNormal:
  │   2239 `partsBetwn`，spine 形）；本文件落**链形包装** `partsBetwnChain`：
  │   normal_list（链）∧ parts L r = sp ∧ … ⇒ parts L (betwn r (LAST py) (HD pz))
  │   = betwn (parts L r) py pz（= HOL 结论逐字，partsSpine→parts 桥一发）。
  │ :590  `normal_condition_last_parts`（38L）→ 树内 `normalConditionLastParts`
  │   （spine 形）；本文件落链形包装 `normalConditionLastPartsChain`。
  │ （`core` 的 `(FST o HD)` 读法）→ `coreEqCoreSpine`：core = coreSpine
  │   （parts 原子非空，headD (0,0) = head! 逐原子；主件 core 代数的换形件）。
  └────────────────────────────────────────────────────────────────

  ┌─ 本波（ml1 W1）与拆波表 ─────────────────────────────────────────
  │ W1（本文件，叶件/链桥）：betwnCat0 + partsBetwnChain +
  │   normalConditionLastPartsChain + coreEqCoreSpine。
  │ W2a/W2b/W3/W4：主机 8b `coreSplitNormalList` 本体（HOL :2028-:3091，
  │   1,064L）按 y 侧/z 侧/装配拆四段（估行见 DELIVERY_ml1 §拆波表）。
  │ W5（并行独立）：r_rtrans_eq 簇（indexf_ztrans_lt 46 + r_rtrans_eq_thm 358
  │   + concl 8；mem_prev_power/sym_power_prev_next 已落）。
  └────────────────────────────────────────────────────────────────

  ┌─ 查重与复用 ─────────────────────────────────────────────────────
  │ `betwn_cat`（:1136）= 树内 `TameSpine.betwnCat`（Reduction3CoreSplitNormal:225，
  │   泛 α [DecidableEq]，本波模板）；本波 `betwnCat0` 是其**后缀版**（cat s g）。
  │ HOL 的 `next_cat_power1/2`、`indexf_cat*`、`MEM_betwn_cat*`、`LAST_betwn_cat*`、
  │ `next_betwn_cat*` 是 HOL betwn_cat/cat_betwn_same 的**内部证体机器**；树内
  │ betwnCat/catBetwnSame 已走独立路线（betwn_betwn_cat 注释记「三子件不需要」），
  │ 故本波**不移植**（判词表记 ◐/免做）。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.TameSpine.Reduction3CoreSplitNormal
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction4
import Kepler.Text.MoreLemma2Island2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (between fgraph)
open Kepler.Assembly (GoodList nextEl fList eList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (normalList)

/-! ## §1 `betwn_cat0`（More_lemma1.hl:1147）后缀版 -/

/-- **HOL `betwn_cat0`**（More_lemma1.hl:1147）：把 `betwn_cat`（前缀 `cat g s`）
换到后缀 `cat s g`；y,z ∈ s 时 `betwn` 只看含 y,z 的前缀段。
证：`indexf` 判定化归 `s.idxOf y < s.idxOf z`（与 `betwnCat` 同块），
`(s++g).idxOf` 经 `idxOf_append` 的 `if_pos` 归一，`between_eq_take_of_idxOf_lt`
双侧后用 `drop_append_of_le_length` + `take_append_of_le_length` 把 g 截掉。 -/
theorem betwnCat0 {α : Type*} [DecidableEq α] [Inhabited α]
    {s g : List α} {y z : α}
    (hnd : (s ++ g).Nodup) (hy : y ∈ s) (hz : z ∈ s)
    (hle : Kepler.Text.Reduction5.indexf y z s
      ≤ Kepler.Text.Reduction5.indexf y s.getLast! s) (hyz : y ≠ z) :
    between (s ++ g) y z = between s y z := by
  have hnds : s.Nodup := (List.nodup_append.mp hnd).1
  have hne : s ≠ [] := by
    intro h
    subst h
    simp at hy
  have hyi : s.idxOf y < s.length := List.idxOf_lt_length_iff.mpr hy
  have hzi : s.idxOf z < s.length := List.idxOf_lt_length_iff.mpr hz
  have hidxne : s.idxOf y ≠ s.idxOf z := fun he => hyz ((List.idxOf_inj hy).mp he)
  have hlastmem : s.getLast! ∈ s := by
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast hne,
      Option.getD_some]
    exact List.getLast_mem hne
  have hgl : s.getLast! = s[s.length - 1]'(by omega) := by
    rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast hne,
      Option.getD_some]
    exact List.getLast_eq_getElem hne
  have hidxlast : s.idxOf s.getLast! = s.length - 1 := by
    conv_lhs => rw [hgl]
    exact Kepler.Text.TameLp.idxOf_getElem hnds (i := s.length - 1) (by omega)
  have hval : ∀ (u v : α), u ∈ s → v ∈ s →
      Kepler.Text.Reduction5.indexf u v s
        = (s.idxOf v + (s.length - s.idxOf u)) % s.length := by
    intro u v hu hv
    unfold Kepler.Text.Reduction5.indexf
    rw [if_pos ⟨hu, hv⟩]
  have hlt : s.idxOf y < s.idxOf z := by
    by_contra hcon
    push Not at hcon
    have hzy : s.idxOf z < s.idxOf y := lt_of_le_of_ne hcon (Ne.symm hidxne)
    rw [hval y z hy hz, hval y s.getLast! hy hlastmem, hidxlast] at hle
    have e1 : (s.idxOf z + (s.length - s.idxOf y)) % s.length
        = s.length - (s.idxOf y - s.idxOf z) := by
      rw [show s.idxOf z + (s.length - s.idxOf y)
          = s.length - (s.idxOf y - s.idxOf z) from by omega,
        Nat.mod_eq_of_lt (by omega)]
    have e2 : (s.length - 1 + (s.length - s.idxOf y)) % s.length
        = s.length - 1 - s.idxOf y := by
      rw [show s.length - 1 + (s.length - s.idxOf y)
          = s.length + (s.length - 1 - s.idxOf y) from by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [e1, e2] at hle
    omega
  have hy' : (s ++ g).idxOf y = s.idxOf y := by
    rw [List.idxOf_append, if_pos hy]
  have hz' : (s ++ g).idxOf z = s.idxOf z := by
    rw [List.idxOf_append, if_pos hz]
  have hlt' : (s ++ g).idxOf y < (s ++ g).idxOf z := by
    rw [hy', hz']
    exact hlt
  rw [Kepler.Text.Reduction4.between_eq_take_of_idxOf_lt hnd
        (List.mem_append_left g hy) (List.mem_append_left g hz) hlt',
      Kepler.Text.Reduction4.between_eq_take_of_idxOf_lt hnds hy hz hlt, hy', hz']
  rw [List.drop_append_of_le_length (by omega : s.idxOf y + 1 ≤ s.length)]
  rw [List.take_append_of_le_length (by rw [List.length_drop]; omega)]

/-! ## §2 `parts_betwn`（More_lemma1.hl:471）链形包装 -/

/-- **HOL `parts_betwn`**（More_lemma1.hl:471）链形：树内 `partsBetwn`
（Reduction3CoreSplitNormal:2239，spine 形）经 `parts_eq_partsSpine` +
`normalList_iff_normalListSpine` 折回链层陈述。结论 RHS 用 `sp`（树内形）；
`hsp : parts L r = sp` 下与 HOL 的 `betwn (parts L r) py pz` 逐字等同。 -/
theorem partsBetwnChain (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} (hn : normalList L hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    {r : List Dart} (hr : r ∈ N) {sp : List (List Dart)} (hsp : parts L r = sp)
    (hunq : (sp.map (fun q => q.head!.1)).Nodup)
    {py pz : List Dart} (hpy : py ∈ sp) (hpz : pz ∈ sp)
    {y z : Dart} (hy : y ∈ py) (hz : z ∈ pz) (hyz : y.1 ≠ z.1) :
    parts L (between r py.getLast! pz.head!) = between sp py pz := by
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hn
  have hspS : Kepler.Text.TameSpine.partsSpine L r = sp := by
    rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine L r]
    exact hsp
  have h := Kepler.Text.TameSpine.partsBetwn L hL hnS hnedg hr hspS hunq
    hpy hpz hy hz hyz
  rwa [← Kepler.Text.ChainBridge.parts_eq_partsSpine L
    (between r py.getLast! pz.head!)] at h

/-! ## §3 `normal_condition_last_parts`（More_lemma1.hl:590）链形包装 -/

/-- **HOL `normal_condition_last_parts`**（More_lemma1.hl:590）链形：
树内 `normalConditionLastParts`（Reduction3CoreSplitNormal:1160，spine 形）
经两桥折回链层（逐字同 HOL）。 -/
theorem normalConditionLastPartsChain (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} (hn : normalList L hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    {r : List Dart} (hr : r ∈ N) {p : List Dart} (hp : p ∈ parts L r)
    {d : Dart} (hd : d ∈ p) :
    (¬ (nextEl r d = fList L (eList d)) ↔ d = p.getLast!) := by
  have hnS : Kepler.Text.TameSpine.NormalListSpine hL N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine L hL N).mp hn
  have hpS : p ∈ Kepler.Text.TameSpine.partsSpine L r := by
    rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine L r]
    exact hp
  exact Kepler.Text.TameSpine.normalConditionLastParts L hL hnS hnedg hr hpS hd

/-! ## §4 `core` 的 spine 形（`(FST o HD)` 读法） -/

/-- `core L r = coreSpine L r`（parts 原子非空 ⇒ `headD (0,0) = head!` 逐原子；
`parts_eq_partsSpine` 换载体）。主件 8b 的 core 代数在 `(FST o HD)` 形与链
`headD` 形之间换形用。**查重记档**：`T4TheoryB.lean:69` 有同名 **private** 同证
（跨模块不可见），本件公开化重落（先例：`nextElInj`）。 -/
theorem coreEqCoreSpine (L : fgraph ℕ) (r : List Dart) :
    core L r = Kepler.Text.TameSpine.coreSpine L r := by
  unfold core Kepler.Text.TameSpine.coreSpine
  rw [Kepler.Text.ChainBridge.parts_eq_partsSpine L r]
  apply List.map_congr_left
  intro p hp
  have hne : p ≠ [] := by
    rw [← Kepler.Text.ChainBridge.parts_eq_partsSpine L r] at hp
    exact Kepler.Text.MoreLemma2Island2.partsAllNonnil L r p hp
  cases p with
  | nil => exact absurd rfl hne
  | cons a t => rfl

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.betwnCat0
#print axioms Kepler.Text.Reduction5.partsBetwnChain
#print axioms Kepler.Text.Reduction5.normalConditionLastPartsChain
#print axioms Kepler.Text.Reduction5.coreEqCoreSpine
