/-
  JcajyduAqLeaf8W2aB — AQ8 波 2a-ii：`last_parts_z1_not_betwn` + `last_parts_z1_not_cat`。

  ┌─ 件目与 HOL 锚 ───────────────────────────────────────────────
  │ ① aq8w2a_lastPartsZ1NotBetwn  AQ8.hl:1506（91 行）
  │ ② aq8w2a_lastPartsZ1NotCat    AQ8.hl:1597（20 行）
  └────────────────────────────────────────────────────────────────

  ┌─ 内容级去重（全 2 名；全闭包负探针 probe_aq8w2aii.log）───────
  │ ① 目标名与旧驼峰名全 Unknown（import 到 JcajyduAqLeaf8W2a +
  │    TameList18/TameList17/JcajyduRed2Trans/TameList3；AGENTS §7.1 #18）。
  │ ② 引擎全在库、标准三：`indexfBetwnEq`/`indexfAddBetwn`/`indexfAddLeft`/
  │    `indexfAntisym`/`indexfN`（TameList3）、`indexfEqInParts`（W0）、
  │    `nextElPartsPower`（TameList10）、`memPowerNextEl`（BetwnBase）、
  │    `idxOfGetLast`（TameList9）、`partsFst`（TameList10）、
  │    `nextEl_mem_of_mem`/`prevEl_mem_of_mem`（TameLp）、`betwnMem`、
  │    `fstEqNextYtransV0`/`fstEqPrevZtransV0`（W0.5）、
  │    `aqs_fstYNeFstZ` + `aq8w2a_lastPartsZ1Not{Y1,Z1}`（W2a-i，本批复用）。
  │ ③ **无条件/常态形**：无 condition 槽；IsMarked 解禁路径直接消费。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字对齐消费点）───────────────────────────
  │ ① 同 W2a-i：y/y1/z/z1 命名等式前件折叠为具体项
  │    （y1 = nextEl r (lYSpine)，z1 = prevEl r (lZSpine)，LAST ↦ getLast!）。
  │ ② 结论 `~(MEM (LAST p) (betwn r y1 z1))` ↦
  │    `p.getLast! ∉ between r (nextEl r (lYSpine)) (prevEl r (lZSpine))`；
  │    not_cat 右结合 `[y1] ++ (betwn r y1 z1 ++ [z1])` 与 HOL APPEND 形同。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（HOL 逐句）─────────────────────────────────────────────
  │ not_betwn：反设 LAST p ∈ betwn r y1 z1。
  │ - 分支 y1 = z1：由 FST_EQ_NEXT/PREV 链 y1.1 = y.1、z1.1 = z.1 得
  │   FST y = FST z，撞 QRDYXYJ_list（aqs_fstYNeFstZ）——y1 = z1 不可能。
  │ - 主支：`indexfBetwnEq` 给 indexf y1 LAST < indexf y1 z1 +
  │   `indexfAddBetwn` 给 indexf LAST z1 ≤ indexf y1 z1；两条
  │   `indexfAntisym`（用 not_z1 保 LAST ≠ z1、y1 ≠ z1）反推
  │   indexf z1 y1 ≤ indexf z1 LAST；`indexfEqInParts` + `idxOfGetLast` +
  │   `indexfAddLeft` 得 idxOf z1 p + indexf z1 y1 < p.length；`indexfN` +
  │   `nextElPartsPower` + `memPowerNextEl` 把 y1 拉进 p；partsFst 两侧
  │   同首点 → FST y = FST z 矛盾（同上）。
  │ not_cat：MEM_APPEND 三段分解，依次交 not_y1/not_betwn/not_z1。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w2a_` 前缀，私件同前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W2a
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList18
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl nextEl_mem_of_mem
  prevEl_mem_of_mem)

/-! ## §0 私件：getLast! 成员 -/

/-- `s ≠ [] ⇒ s.getLast! ∈ s`（per-file-private 约定零共享）。 -/
private theorem aq8w2a_getLastMem {α : Type} [Inhabited α] {s : List α}
    (h : s ≠ []) : s.getLast! ∈ s := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-! ## §1 `last_parts_z1_not_betwn`（HOL AQ8.hl:1506） -/

/-- HOL `last_parts_z1_not_betwn`（AQ8.hl:1506）：part 末元不在
`betwn r y1 z1`（y1 = nextEl r l'y，z1 = prevEl r l'z）。 -/
theorem aq8w2a_lastPartsZ1NotBetwn (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    {p : List (ℕ × ℕ)}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hp : p ∈ partsSpine L r) (hz1p : prevEl r (lZSpine L N r x) ∈ p) :
    p.getLast! ∉ between r (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) := by
  intro hmem
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hn : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hrN
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hpun : p.Nodup := partsUniq L hr1 hr2 p hp
  have hlastmem : p.getLast! ∈ p := aq8w2a_getLastMem hpne
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy1r : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hyr
  have hz1r : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hzr
  have hfstNext := fstEqNextYtransV0 L hL hgn hm hf
  have hfstPrev := fstEqPrevZtransV0 L hL hgn hm hf
  have hneLastZ1 : p.getLast! ≠ prevEl r (lZSpine L N r x) :=
    aq8w2a_lastPartsZ1NotZ1 L hL hgn hm hf hp hz1p
  -- 分支 y1 = z1 直接撞 FST（y1.1 = y.1、z1.1 = z.1）
  by_cases hy1z1 : nextEl r (lYSpine L r x) = prevEl r (lZSpine L N r x)
  · exfalso
    exact aqs_fstYNeFstZ L hL hgn hunL hm hf
      (hfstNext.symm.trans ((congrArg (fun d => d.1) hy1z1).trans hfstPrev))
  -- 主支：indexf 算术链（同 W1a not_betwn，端点换 y1/z1）
  have hlt1 : indexf (nextEl r (lYSpine L r x)) (p.getLast!) r <
      indexf (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) r :=
    ((indexfBetwnEq hy1z1 hr1 hy1r hz1r).mp hmem).2
  have hadd := indexfAddBetwn hy1z1 hr1 hy1r hmem hz1r
  have hle : indexf (p.getLast!) (prevEl r (lZSpine L N r x)) r ≤
      indexf (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x)) r := by
    omega
  have hlastr : p.getLast! ∈ r := betwnMem hmem
  have hanti1 : indexf (p.getLast!) (prevEl r (lZSpine L N r x)) r +
      indexf (prevEl r (lZSpine L N r x)) (p.getLast!) r = r.length :=
    indexfAntisym hlastr hz1r hneLastZ1
  have hanti2 : indexf (nextEl r (lYSpine L r x))
      (prevEl r (lZSpine L N r x)) r +
      indexf (prevEl r (lZSpine L N r x)) (nextEl r (lYSpine L r x)) r
      = r.length :=
    indexfAntisym hy1r hz1r hy1z1
  have hle2 : indexf (prevEl r (lZSpine L N r x)) (nextEl r (lYSpine L r x)) r ≤
      indexf (prevEl r (lZSpine L N r x)) (p.getLast!) r := by
    omega
  have hidxZ1 : indexf p.head! (prevEl r (lZSpine L N r x)) r =
      p.idxOf (prevEl r (lZSpine L N r x)) :=
    indexfEqInParts L hn hrN hz1p hp
  have hidxLast : indexf p.head! (p.getLast!) r = p.idxOf (p.getLast!) :=
    indexfEqInParts L hn hrN hlastmem hp
  have hidxLast2 : p.idxOf (p.getLast!) = p.length - 1 := idxOfGetLast hpun hpne
  have hz1lt : p.idxOf (prevEl r (lZSpine L N r x)) < p.length :=
    List.idxOf_lt_length_iff.mpr hz1p
  have hheadmem : p.head! ∈ p := List.head!_mem_self hpne
  have hheadr : p.head! ∈ r := memPartsImp L hr1 hr2 hp p.head! hheadmem
  have hyle : indexf p.head! (prevEl r (lZSpine L N r x)) r ≤
      indexf p.head! (p.getLast!) r := by
    rw [hidxZ1, hidxLast, hidxLast2]
    omega
  have haddleft := indexfAddLeft hheadr hz1r hlastr hyle
  have hsum : p.idxOf (prevEl r (lZSpine L N r x)) +
      indexf (prevEl r (lZSpine L N r x)) (p.getLast!) r = p.length - 1 := by
    rw [← hidxZ1, haddleft, hidxLast, hidxLast2]
  have hltk : p.idxOf (prevEl r (lZSpine L N r x)) +
      indexf (prevEl r (lZSpine L N r x)) (nextEl r (lYSpine L r x)) r
      < p.length := by omega
  have hpower := nextElPartsPower L hr1 hr2 hp hz1p
    (indexf (prevEl r (lZSpine L N r x)) (nextEl r (lYSpine L r x)) r) hltk
  have hnextn : (nextEl r)^[indexf (prevEl r (lZSpine L N r x))
      (nextEl r (lYSpine L r x)) r] (prevEl r (lZSpine L N r x))
      = nextEl r (lYSpine L r x) := indexfN hz1r hy1r hr1
  have hinp : (nextEl p)^[indexf (prevEl r (lZSpine L N r x))
      (nextEl r (lYSpine L r x)) r] (prevEl r (lZSpine L N r x)) ∈ p :=
    memPowerNextEl hz1p _
  have hy1mem : nextEl r (lYSpine L r x) ∈ p := by
    have h := hinp
    rw [← hpower, hnextn] at h
    exact h
  have hfst1 : (nextEl r (lYSpine L r x)).1 = p.head!.1 :=
    partsFst L hL hn hrN hp hy1mem
  have hfst2 : (prevEl r (lZSpine L N r x)).1 = p.head!.1 :=
    partsFst L hL hn hrN hp hz1p
  exact aqs_fstYNeFstZ L hL hgn hunL hm hf
    (hfstNext.symm.trans (hfst1.trans (hfst2.symm.trans hfstPrev)))

/-! ## §2 `last_parts_z1_not_cat`（HOL AQ8.hl:1597） -/

/-- HOL `last_parts_z1_not_cat`（AQ8.hl:1597）：part 末元不在
`[y1] ++ (betwn r y1 z1 ++ [z1])`——由 not_y1 / not_betwn / not_z1 分解直收。 -/
theorem aq8w2a_lastPartsZ1NotCat (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    {p : List (ℕ × ℕ)}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hp : p ∈ partsSpine L r) (hz1p : prevEl r (lZSpine L N r x) ∈ p) :
    p.getLast! ∉ [nextEl r (lYSpine L r x)] ++
      (between r (nextEl r (lYSpine L r x)) (prevEl r (lZSpine L N r x))
        ++ [prevEl r (lZSpine L N r x)]) := by
  intro hmem
  rcases List.mem_append.mp hmem with h1 | h1
  · rw [List.mem_singleton] at h1
    exact aq8w2a_lastPartsZ1NotY1 L hL hgn hm hf hp hz1p h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · exact aq8w2a_lastPartsZ1NotBetwn L hL hgn hm hf hp hz1p h2
    · rw [List.mem_singleton] at h2
      exact aq8w2a_lastPartsZ1NotZ1 L hL hgn hm hf hp hz1p h2

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w2a_lastPartsZ1NotBetwn
#print axioms Kepler.Text.TameSpine.aq8w2a_lastPartsZ1NotCat
