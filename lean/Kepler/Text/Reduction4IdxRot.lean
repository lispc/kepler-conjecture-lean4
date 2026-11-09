/-
  Kepler.Text.Reduction4IdxRot — J 战役 J1-B4：`rot_parts`（reduction4.hl:4004）。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ reduction4.hl:4004 `rot_parts`
  │   `good_list L ∧ normal_list L N ∧ MEM r N ∧ MEM p (parts L r)
  │    ==> ?k. take (sizel p) (rot k r) = p`
  │   → rotParts
  │ 依赖（全部已落库）：
  │   normalList（ChainListsL1）、partsFlatten/partsNonnil/uniqParts（M0e）、
  │   partsUniqNonnil（片 3）、flattenRot（B3 Reduction4Idx:58）。
  │ 实现：k = (parts L r).idxOf p（rotate_eq_drop_append_take + getElem_idxOf
  │ 取头），再 flattenRot 把 (parts.rotate k).flatten 换成 r.rotate k₂，
  │ flatten (p :: rest) = p ++ …，最后 take_left 收口。
  │ 注：mem_ifbetwn_hd / mem_ifbetwn_tl_extend（:4046/:4123）本轮不做——
  │ 其证体经 `ifbetwn_indexf` → `Reduction2.indexf_rotn_alt`（J2 锁）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL1
import Kepler.Text.Reduction4
import Kepler.Text.Reduction4Idx
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4IdxRot

open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart parts)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.Reduction4Idx (flattenRot)
open Kepler.Text.MoreLemma2Island2 (partsFlatten partsAllNonnil partsNonnil uniqParts)
open Kepler.Text.MoreLemma2Island3 (partsUniqNonnil)
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (getElem_idxOf)

/-- **HOL `rot_parts`**（reduction4.hl:4004
`good_list L ∧ normal_list L N ∧ MEM r N ∧ MEM p (parts L r) ==>
  ?k. take (sizel p) (rot k r) = p`）。
即：`p` 是 `r` 的某个旋转的前缀。 -/
theorem rotParts (L : fgraph ℕ) (hL : GoodList L) {N : List (List Dart)}
    (hN : normalList L hL N) {r : List Dart} (hr : r ∈ N) {p : List Dart}
    (hp : p ∈ parts L r) :
    ∃ k : ℕ, (r.rotate k).take p.length = p := by
  have hun : r.Nodup := (List.nodup_flatten.mp hN.1).1 r hr
  have hne : r ≠ [] := hN.2.1 r hr
  have hpne : p ≠ [] := partsAllNonnil L r p hp
  have hpartsNe : parts L r ≠ [] := partsNonnil L hne
  -- 索引可界：`k = idxOf p (parts L r)` 落在表内
  have hklt : (parts L r).idxOf p < (parts L r).length :=
    List.idxOf_lt_length_iff.mpr hp
  -- `parts.rotate k` 的首段就是 `p`（drop 非空，用 cons 形分解取头）
  have hcons : (parts L r).rotate ((parts L r).idxOf p)
      = p :: ((parts L r).drop ((parts L r).idxOf p + 1) ++
              (parts L r).take ((parts L r).idxOf p)) := by
    rw [List.rotate_eq_drop_append_take (Nat.le_of_lt hklt),
      List.drop_eq_getElem_cons hklt, getElem_idxOf hp]
    rfl
  -- flatten 换形：`flatten (p :: rest) = p ++ rest.flatten`
  obtain ⟨k2, hk2⟩ := flattenRot ((parts L r).idxOf p) (parts L r)
  have hfl : ((parts L r).rotate ((parts L r).idxOf p)).flatten
      = p ++ ((parts L r).rotate ((parts L r).idxOf p)).tail.flatten := by
    rw [hcons]
    rfl
  -- 把 flatten 等式换成 `r.rotate k2` 的等式
  have hrot : r.rotate k2
      = p ++ ((parts L r).rotate ((parts L r).idxOf p)).tail.flatten := by
    have h1 : ((parts L r).rotate ((parts L r).idxOf p)).flatten = r.rotate k2 := by
      rw [hk2, partsFlatten L hun hne]
    exact h1.symm.trans hfl
  -- 收口：`take` 只取前缀 `p`
  refine ⟨k2, ?_⟩
  rw [hrot]
  exact List.take_left

end Kepler.Text.Reduction4IdxRot

/-! 公理审计锚（本文件编译即执行；预期 = 标准三或更弱，零 sorryAx。） -/
#print axioms Kepler.Text.Reduction4IdxRot.rotParts
