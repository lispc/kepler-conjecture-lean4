/-
  Kepler.Text.TameSpine.JcajyduAqLeaf12Y — AQ12 叶 W-F3e-i（decl 68 主证骨架 + final 支 + 合取 1）。

  HOL：AQ12.hl:3643-:4092 `AQ12_concl`（444 行）的**第一合取**
  （`flag_list` 首合取：FinalDartList 内任两元 u→v 存在 contour，支撑仍在
  FinalDartList）。

  件目/依赖（开工报价）：主证骨架 + final 支 + 合取 1；估 60–120（≤240）。
  · 依赖：`ntransId`/`ntrans1`（JcajyduRed2Trans）、`MarkedListSpineFull.2.1`
    （TameList13:268）、decl 54 `aqs_existsContourCombinatoric`（12S）、
    `aq4`（**JcajyduAqLeaf4W3b.lean:28，已落库**）。
  · **本件是 AQ12 叶 `h4 : aq4Concl` 七个条件槽消费点的唯一消槽处**：
    非 final 支调 decl 54 时以 `h4 := aq4 L hL` 直接消槽（源码内 ★ 标注）。
    **AQ4 落库后此处首次消槽**；自此 AQ12 的 7 个 h4 条件槽件不再有未消槽
    的消费点（12S 是最后一个携带 h4 前提的件，其消费者即本件）。
  · **12Y 不宣称 `aq12` 收口**：合取 2 的 N/S 支在 12Z、F 支在 12AA。
  · 合取 1 **无需** `finalListSpine L (rtrans 1)` 前提（final 支用 `hfin`，
    非 final 支只用行 r1/r2 ∈ filter 的 final；HOL 主证同此，`hfinal` 只喂
    合取 2 的 r'=rtrans 槽）。

  陈述对表（与 TowerBase:307 `aq12Concl` 逐字对应）：
  `aq12Concl = ∀ N r x, hgn → hm → final (rtrans 1) → FlagListSpine L (ntrans 1)`；
  `FlagListSpine`（TameList13:243）= `合取1 ∧ 合取2`；
  本件 = `∀ u ∈ FinalDartListSpine L (ntrans 1), ∀ v ∈ ..., ∃ s, Contour ∧
  s ≠ [] ∧ s.head! = u ∧ s.getLast! = v ∧ ∀ z ∈ s, z ∈ FinalDartListSpine L (ntrans 1)`。
  final 支投影路径（下游复用）：`hm : MarkedListSpineFull hL N r x`
  = `MarkedListSpine ∧ (final → FlagListSpine L N) ∧ (¬final → SFlagListSpine ...)`，
  故 `hm.2.1 hfin : FlagListSpine L N`，其 `.1` 即首合取。

  纪律：零 sorry/admit/native_decide/axiom；既有文件零触碰；主仓 tracked 零改动。
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf12S
import Kepler.Text.TameSpine.JcajyduAqLeaf4W3b

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Kepler.Text.TameSpine

open Classical
open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts eList fList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-! ## §1 decl 68 首合取（主证骨架 + final 支 + 合取 1） -/

/-- **HOL `AQ12_concl` 首合取**（AQ12.hl:3643-:4092 的 `flag_list` 第一合取）：
`FinalDartList N'` 内任两元 u→v 之间存在 contour，支撑 ⊆ `FinalDartList N'`。 -/
theorem aq12y_flagListConjunctOne (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) :
    ∀ u : ℕ × ℕ, u ∈ FinalDartListSpine L (ntransSpine L N r x 1) →
      ∀ v : ℕ × ℕ, v ∈ FinalDartListSpine L (ntransSpine L N r x 1) →
      ∃ s : List (ℕ × ℕ), ContourListSpine L s ∧ s ≠ [] ∧ s.head! = u ∧
        s.getLast! = v ∧
        ∀ z ∈ s, z ∈ FinalDartListSpine L (ntransSpine L N r x 1) := by
  intro u hu v hv
  by_cases hfin : finalListSpine L r
  · -- final 支：`ntrans 1 = N`；`hm.2.1 hfin : FlagListSpine L N` 首合取直取
    rw [ntransId L N r x hfin] at hu hv ⊢
    exact (hm.2.1 hfin).1 u hu v hv
  · -- 非 final 支：`ntrans 1 = replace r [S] N ++ [F]`，行来源两分
    have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
    -- canonical split（ntrans1 的写形）↔ f-split（decl 54 的写形）
    have hfindcanon : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
      aq10_memFindFaceImpFacesEq hL.1 (pplhuljV0 L hL hgn hunL hm hfin).1
    have hsplit_eq : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (prevEl r (lZSpine L N r x)))
        = splitNormalListSpine L r (findFaceDarts L x) (lYSpine L r x)
          (prevEl r (lZSpine L N r x)) := by
      rw [hfindcanon]
    have hn : ntransSpine L N r x 1
        = replaceSpine r [(splitNormalListSpine L r (findFaceDarts L x)
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).2] N
          ++ [(splitNormalListSpine L r (findFaceDarts L x)
            (lYSpine L r x) (prevEl r (lZSpine L N r x))).1] := by
      rw [ntrans1 L N r x hfin, hsplit_eq]
    -- u、v 各自落在最终行 l1/l2（filter final 的展平成员）
    obtain ⟨l1, hl1, hu1⟩ := List.mem_flatten.mp hu
    obtain ⟨hl1N, hl1fin⟩ := List.mem_filter.mp hl1
    have hfin1 : finalListSpine L l1 := decide_eq_true_iff.mp hl1fin
    obtain ⟨l2, hl2, hv2⟩ := List.mem_flatten.mp hv
    obtain ⟨hl2N, hl2fin⟩ := List.mem_filter.mp hl2
    have hfin2 : finalListSpine L l2 := decide_eq_true_iff.mp hl2fin
    -- ★ AQ4 消槽点（W-F3e-i 唯一消槽）：`h4 : aq4Concl L hL := aq4 L hL`
    --   （`aq4` 于 JcajyduAqLeaf4W3b.lean:28 落地；此处为 AQ12 叶首个也是
    --   最后一个 h4 消费点，7 个 h4 条件槽件的消费链在此收束。）
    obtain ⟨s, hcs, hne, hhd, hlast, hsub⟩ :=
      aqs_existsContourCombinatoric L hL hgn (aq4 L hL) hm hfin
        (findFaceDarts L x) rfl rfl rfl hfin1 hfin2 (hn ▸ hl1N) (hn ▸ hl2N)
        rfl hv2 hu1
    refine ⟨s, hcs, hne, hhd, hlast, ?_⟩
    intro z hz
    rw [hn]
    exact hsub hz

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期标准三 `[propext, Classical.choice, Quot.sound]`，
零 sorryAx。） -/
#print axioms Kepler.Text.TameSpine.aq12y_flagListConjunctOne
