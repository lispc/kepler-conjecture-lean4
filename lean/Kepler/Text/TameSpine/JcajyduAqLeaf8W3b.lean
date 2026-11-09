/-
  JcajyduAqLeaf8W3b — AQ8 波 3b-i：snd 巨头 CASE 1 引擎之一（`MEM` 桥）。

  ┌─ 本波范围（按令：W3b 超线则先交 `MEM` 桥，提 finer part 留 W3b-i-2）──
  │ ① aq8w3b_arcSubset        闭弧 `s = [z] ++ betwn r z y ++ [y]` 的元素全在 r
  │ ② aq8w3b_partsFstHdMemSub GSUBGOAL#1（AQ8.hl:950-990）：
  │    `MEM d (MAP (FST o HD) (parts L s)) ⇒ MEM d (MAP (FST o HD) (parts L r))`
  │ 两件均为 CASE 1（`betwn (find_face L y) y z = []` 支，此时
  │ `s = SND split`，故 `s ∈ ntrans … 1` 由 `sndMemRtran1` 供——本波以
  │ `hsN` 槽显式接过）。
  └────────────────────────────────────────────────────────────────

  ┌─ 证明内核（HOL 逐句）─────────────────────────────────────────
  │ `d = FST (HD p)`（`p ∈ parts L s`）⇒ `HD p ∈ p`（part 非空）
  │ ⇒ `HD p ∈ s`（`parts_darts`，line 级）⇒ `HD p ∈ r`（①，弧 ⊆ r）
  │ ⇒ `parts_mem_exists` 给 `p' ∈ parts L r` 含 `HD p`
  │ ⇒ `parts_fst` 两次（s 侧、r 侧）给 `FST (HD p) = FST (HD p')`
  │ ⇒ `d ∈ MAP (FST o HD) (parts L r)`。
  │ 关键载体：`partsFst`（TameList10:442，`x ∈ p ⇒ x.1 = p.head!.1`，
  │ 即 part 内全同 node 首点）——HOL 只消费一次，Lean 亦只一次。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）─────────────────────────────────────────────
  │ ① `AQ_normal_list` → `aqs_aqNormalList`（W1a:113）**五塔接口槽**
  │    `h1..h5 : aq1Concl…aq5Concl`（编排者 2026-11-09 裁决：与 W1a 同口径，
  │    塔接口槽、非新数学前提，塔顶 13 前提 ⇒ 无条件形时消去）。
  │ ② HOL `MEM (APPEND [z] (APPEND (betwn r z y) [y]))` 的窗口以
  │    `harc` 等式槽承接（本件对 `s` 抽象，CASE 1 两支共用）。
  │ ③ `FST o HD` ↦ `fun p => p.head!.1`（parts 件非空，`HD` 在非空面上同值）。
  │ ④ `uniq`/`all`/`MEM`/`MAP`/`LAST` 逐字折算；`hL`/`hgn`/`hm`/`hf` 显式。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件 `aq8w3b_` 前缀。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3
import Kepler.Text.TameSpine.JcajyduBetwnMap

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 闭弧的元素扇出（`s ⊆ r`） -/

/-- 闭弧 `s = [z] ++ between r z y ++ [y]`（`z = l'z`、`y = l'y`）的元素
全部落在 `r` 中：首尾两支是 `z`/`y` 本身，中间支 `betwnMem`。 -/
theorem aq8w3b_arcSubset (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {s : List (ℕ × ℕ)}
    (harc : s = [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) :
    ∀ a ∈ s, a ∈ r := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  intro a ha
  rw [harc] at ha
  rcases List.mem_append.mp ha with h1 | hy'
  · rcases List.mem_append.mp h1 with hz' | hb
    · rw [List.mem_singleton] at hz'
      subst hz'
      exact hz
    · exact betwnMem hb
  · rw [List.mem_singleton] at hy'
    subst hy'
    exact hy

/-! ## §1 `MEM` 桥（GSUBGOAL#1，AQ8.hl:950-990） -/

/-- **HOL GSUBGOAL#1**（AQ8.hl:950）：
`!d. MEM d (MAP (FST o HD) (parts L s)) ==> MEM d (MAP (FST o HD) (parts L r))`。

`d = FST (HD p)`、`p ∈ parts L s` ⇒ `HD p ∈ r`（`partsDarts` + §0）
⇒ `partsMemExists` 取含它的 `p' ∈ parts L r` ⇒ `partsFst` 两侧给
`FST (HD p) = FST (HD p')`。`s ∈ ntrans … 1`（`hsN`，CASE 1 由
`sndMemRtran1` 供）与五塔接口槽供 `normal_list L (ntrans … 1)`。 -/
theorem aq8w3b_partsFstHdMemSub (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {s : List (ℕ × ℕ)}
    (harc : s = [lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x])
    (hsN : s ∈ ntransSpine L N r x 1) :
    ∀ d, d ∈ (partsSpine L s).map (fun p => p.head!.1) →
      d ∈ (partsSpine L r).map (fun p => p.head!.1) := by
  intro d hd
  obtain ⟨p, hp, hpd⟩ := List.mem_map.mp hd
  -- 语境
  have hnN : NormalListSpine hL (ntransSpine L N r x 1) :=
    aqs_aqNormalList L hL h1 h2 h3 h4 h5 hgn hm
  have hsn : s.Nodup ∧ s ≠ [] := normalListUniqNonnil hnN hsN
  have hpne : p ≠ [] := partsAllNonnil L hsn.1 hsn.2 p hp
  have hd1p : p.head! ∈ p := List.head!_mem_self hpne
  have hd1s : p.head! ∈ s := memPartsImp L hsn.1 hsn.2 hp p.head! hd1p
  have hd1r : p.head! ∈ r := aq8w3b_arcSubset L hL hgn hm hf harc _ hd1s
  -- r 侧的承载 part
  have hnR : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  have hrnd : r.Nodup := (normalListUniqNonnil hnR hrN).1
  obtain ⟨p', hp', hd1p'⟩ := partsMemExists L hrnd hd1r
  -- part 内全同首点：两侧各一次
  have hfst : (p.head!).1 = p'.head!.1 := partsFst L hL hnR hrN hp' hd1p'
  exact List.mem_map.mpr ⟨p', hp', hfst.symm.trans hpd⟩

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aq8w3b_arcSubset
#print axioms Kepler.Text.TameSpine.aq8w3b_partsFstHdMemSub
