/-
  Kepler.Text.Reduction5J5K4IndexSndX — K4 C2：HOL `final_assumption_index_snd_x`
  （reduction4.hl:4675–4772，本体 98 HOL 行；scout 的 644 行范围把其后的
  `next_el_core_last` 等独立 K4 辅助件一并计入，实际本体远小于估计）。

  ┌─ 依赖核查（派单第 1 条）─────────────────────────────────────────
  │ 本体证体 **零引用** `final_assumption_not_mem_snd_x_fy/_zx`（J4 在飞）：
  │ 对 4675–4772 grep `snd_x` 仅命中定义名本身。真实依赖全部在库：
  │ `core_lt_indexf` ← `coreLtIndexf`（**已落库** Reduction4K4C0R2b1，R2b1 三件之一）；
  │ `FST_next_face_eq_SND` ← `fstNextFaceEqSnd`；`final_assumption_mem_uniq` ←
  │ `finalAssumptionMemUniq`；`fst_yi_ne_fst_zi` ← `fstYiNeFstZi`；
  │ `parts_mem_exists`/`parts_flatten`/`parts_uniq_nonnil` ← `partsMemExists`/
  │ `partsFlatten`/`partsUniqNonnil`；`next_el_parts_last`/`f_list_imp_last` ←
  │ `nextElPartsLast`/`fListImpLast`；`mem_fst_core` ← `memFstCore`；
  │ `DIOWAAS` ← `diowaasR`（W5a）；`indexf0`（:1542 形）← `indexf_eq_zero`；
  │ `uniq_sublist_unique` ← `uniqSublistUnique`。**无需 core_betwn/tl_extend**
  │ （`coreLtIndexf` 本体属 R2b1 已落库件，非 R2b2）。⇒ 直接开写，不转 indexf2。

  ┌─ 路线（HOL 同构，短路线）───────────────────────────────────────
  │ `p` = parts 中包含 x 的块，`p' = next_el (parts L r) p`；`p'.head! = next_el (find_face x) x`
  │ （`nextElPartsLast` + `fListImpLast` + `uniqSublistUnique` 定 LAST p = x）。
  │ 三支：
  │ ① `FST p'.head! = FST (ytrans i)`：左端 indexf = 0（`indexfRefl`），
  │    右端 > 0（`indexf_eq_zero` 反证，用 `fstYiNeFstZi`）；
  │ ② `FST p'.head! = FST (ztrans i)`：右端 = 0，左端 < 0 不可能（omega）；
  │ ③ 其余：`coreLtIndexf` 把 r 上 `DIOWAAS` 不等式搬到 core 首点表。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction4K4C0R2b1
import Kepler.Text.Reduction5J5FstNe
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.MoreLemma2QuotientAlt2
import Kepler.Text.Reduction5J5CoreNextF
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.Reduction4Subseg4
import Kepler.Text.Reduction5Ml1W5a
import Kepler.Text.Reduction1W2e

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- **HOL `final_assumption_index_snd_x`**（reduction4.hl:4675–4772）：
`i < transform_count` 时，`core L r` 上以 `SND x` 起算的 indexf 满足
`ytrans i` 严格在 `ztrans i` 之前。 -/
theorem indexSndX (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    ∀ i, i < k →
      indexf x.2 (ytrans L N r x i).1 (core L r)
        < indexf x.2 (ztrans L N r x i).1 (core L r) := by
  intro i hi
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hi)
  -- 记忆包（HOL final_assumption_mem_uniq）
  obtain ⟨hxd, -, hwf, hwr, hzr_all, hyr_all, hyf_all, hzf_all, -, -, -⟩ :=
    finalAssumptionMemUniq L hL hgn hres haq k hm hnf hk
  have hxr : x ∈ r := hm.2.2.2.1
  have hyr : ytrans L N r x i ∈ r := hyr_all i hi
  have hzr : ztrans L N r x i ∈ r := hzr_all i hi
  have hzf : ztrans L N r x i ∈ findFaceDarts L x := hzf_all i hi
  have hrnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hrne : r ≠ [] := hm.2.1.2.1 r hm.2.2.1
  -- w = nextEl f x 的顶点 = x.2（HOL FST_next_face_eq_SND）
  have hwv : (nextEl (findFaceDarts L x) x).1 = x.2 :=
    fstNextFaceEqSnd L hL hgn hm hnf
  -- parts 块 p 与 p' = next_el (parts) p
  obtain ⟨p, hpmem, hxp⟩ := Kepler.Text.MoreLemma2Naming.partsMemExists L hrnd hxr
  have hxpLast : x ∈ (parts L r).map (fun p => p.getLast!) :=
    fListImpLast L hL hres.edgeNondegenerate hrnd hrne hxd hxr hm.2.2.2.2.2.1
  obtain ⟨p0, hp0mem, hp0last⟩ := List.mem_map.mp hxpLast
  have hfl : (parts L r).flatten.Nodup := by
    rw [Kepler.Text.MoreLemma2Island2.partsFlatten L hrnd hrne]; exact hrnd
  have hp0ne : p0 ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r p0 hp0mem
  have hx0 : x ∈ p0 := by
    rw [← hp0last]
    exact Kepler.Graphs.getLast!_mem hp0ne
  have hpEq : p0 = p :=
    Kepler.Text.MoreLemma2Naming.uniqSublistUnique (parts L r) hfl p0 hp0mem p hpmem
      ⟨x, hx0, hxp⟩
  have hlast : p.getLast! = x := by
    rw [← hpEq]
    exact hp0last
  have hnext : nextEl (findFaceDarts L x) x = nextEl r x := hm.2.2.2.2.2.1.symm
  have hw_eq_head : nextEl (findFaceDarts L x) x
      = (nextEl (parts L r) p).head! := by
    rw [hnext]
    exact Kepler.Text.MoreLemma2QuotientAlt2.nextElPartsLast L hrnd hrne hpmem hxp hlast.symm
  set p' : List Dart := nextEl (parts L r) p with hp'def
  have hp'mem : p' ∈ parts L r := by
    rw [hp'def]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hpmem
  have hp'head : p'.head! = nextEl (findFaceDarts L x) x := by
    rw [hp'def]
    exact hw_eq_head.symm
  -- 首点相异（HOL fst_yi_ne_fst_zi）
  have huv : (ytrans L N r x i).1 ≠ (ztrans L N r x i).1 :=
    fstYiNeFstZi L hL hgn hres haq k i hm hnf hk hi
  -- 三个分支（HOL :4670–4770 的 ASM_CASES 结构）
  by_cases hpu : p'.head!.1 = (ytrans L N r x i).1
  · -- ① FST p'.head! = FST y_i
    have hw1 : (nextEl (findFaceDarts L x) x).1 = (ytrans L N r x i).1 := by
      rw [← hp'head]
      exact hpu
    have hwz : (nextEl (findFaceDarts L x) x).1 ≠ (ztrans L N r x i).1 := by
      rw [hw1]
      exact huv
    have hwcore : (nextEl (findFaceDarts L x) x).1 ∈ core L r :=
      Kepler.Text.Reduction4Idx.memFstCore L hL hm hwr
    have hycore : (ytrans L N r x i).1 ∈ core L r :=
      Kepler.Text.Reduction4Idx.memFstCore L hL hm hyr
    have hzcore : (ztrans L N r x i).1 ∈ core L r :=
      Kepler.Text.Reduction4Idx.memFstCore L hL hm hzr
    have hleft : indexf (nextEl (findFaceDarts L x) x).1 (ytrans L N r x i).1
        (core L r) = 0 := by
      rw [hw1]
      exact Kepler.Text.Reduction4.indexfRefl hycore
    have hpos : 0 < indexf (nextEl (findFaceDarts L x) x).1
        (ztrans L N r x i).1 (core L r) := by
      rcases Nat.eq_zero_or_pos
        (indexf (nextEl (findFaceDarts L x) x).1 (ztrans L N r x i).1 (core L r))
        with h0 | hpos
      · exact absurd (Kepler.Text.Reduction4.indexf_eq_zero hwcore hzcore h0) hwz
      · exact hpos
    rw [← hwv, hleft]
    exact hpos
  · by_cases hpv : p'.head!.1 = (ztrans L N r x i).1
    · -- ② FST p'.head! = FST z_i：r 侧 DIOWAAS 与 indexf_refl 相抵
      have hw1 : (nextEl (findFaceDarts L x) x).1 = (ztrans L N r x i).1 := by
        rw [← hp'head]
        exact hpv
      have hwz_dart : nextEl (findFaceDarts L x) x = ztrans L N r x i :=
        Kepler.Text.Reduction1.simpleList hxd hwf hzf hw1 hunL
      have hdio : indexf (nextEl (findFaceDarts L x) x)
          (ytrans L N r x i) r < indexf (nextEl (findFaceDarts L x) x)
          (ztrans L N r x i) r :=
        diowaasR L hL hgn hm i hfi (w := nextEl (findFaceDarts L x) x) rfl
      have hzeroR : indexf (nextEl (findFaceDarts L x) x)
          (ztrans L N r x i) r = 0 := by
        rw [hwz_dart]
        exact Kepler.Text.Reduction4.indexfRefl hzr
      rw [hzeroR] at hdio
      exact absurd hdio (Nat.not_lt_zero _)
    · -- ③ 常规支：coreLtIndexf + DIOWAAS
      have hdio : indexf (nextEl (findFaceDarts L x) x)
          (ytrans L N r x i) r < indexf (nextEl (findFaceDarts L x) x)
          (ztrans L N r x i) r :=
        diowaasR L hL hgn hm i hfi (w := nextEl (findFaceDarts L x) x) rfl
      have hdio' : indexf p'.head! (ytrans L N r x i) r
          < indexf p'.head! (ztrans L N r x i) r := by
        rw [← hw_eq_head]
        exact hdio
      have hcore := (Kepler.Text.Reduction4.coreLtIndexf L hL (p := p') (u := ytrans L N r x i)
        (v := ztrans L N r x i) hm hyr hzr hpu hpv huv hp'mem).mp hdio'
      rw [hp'head] at hcore
      rw [← hwv]
      exact hcore

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.indexSndX
