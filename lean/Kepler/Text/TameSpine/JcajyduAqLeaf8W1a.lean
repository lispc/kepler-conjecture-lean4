/-
  JcajyduAqLeaf8W1a — AQ8 波 1a：y 族四件 + `AQ_normal_list` 条件槽。

  ┌─ 件目与 HOL 锚 ───────────────────────────────────────────────
  │ ① aqs_aqNormalList        AQ8.hl:39（HOL AQ_normal_list，8 行）
  │ ② aq8w1_lastPartsYNotY    AQ8.hl:185（42 行）
  │ ③ aq8w1_lastPartsYNotZ    AQ8.hl:227（49 行）
  │ ④ aq8w1_lastPartsYNotBetwn AQ8.hl:296（77 行）
  │ ⑤ aqs_lastPartsYNotCat    AQ8.hl:373（13 行）
  └────────────────────────────────────────────────────────────────

  ┌─ 命名（编排者规则）───────────────────────────────────────────
  │ 跨叶消费者（HOL 名共现实测）：`AQ_normal_list` 被 AQ9.hl 7 次 /
  │ AQ12.hl 2 次 / AQ13.hl 2 次调用；`last_parts_y_not_cat` 被
  │ AQ12.hl:2199 调用 ⇒ 此二件用**中立名 `aqs_`**。
  │ `last_parts_y_not_y/z/betwn` 仅 AQ8 自身消费（not_cat 内部用），
  │ 用 `aq8w1_` 前缀。私件两条 `aq8w1_` 前缀。
  └────────────────────────────────────────────────────────────────

  ┌─ 内容级去重（全 5 名；全导入闭包负探针 probe_aq8w1a.log）─────
  │ ① 目标名 5 个全 Unknown（import 到 JcajyduAqLeaf8W05 + TameList18/
  │    TameList17/TowerBase 闭包；AGENTS §7.1 #18）。
  │ ② y 族四件零命中：AQ1 车道未落（Split1D:21-22 只记了 FST 替代路线）；
  │    `normal_list_parts_next_last` 的 Lean 镜 `normalListPartsNextLast`
  │    （TameList10:463）已在库，是 not_y 的唯一引擎。
  │ ③ `AQ_normal_list` 的 HOL 证体 = 一次 SIMP 调 AQ1/AQ2/AQ3/AQ4/AQ5；
  │    Lean 侧五槽即 `aq1Concl…aq5Concl`（TowerBase:227-287）与
  │    `NormalListSpine` 五合取逐位同形 ⇒ 条件槽为纯组装（零新数学）。
  │ ④ 上游 axioms 实测（probe_aq8w1a.log）：`qrdyxyjList`/`markedTranslate`/
  │    `markedListMarked`/`normalListNormal`/`normalListPartsNextLast`
  │    全 = 标准三，无 sorryAx（Split1G:17 的 IsMarked 债记档已过期，
  │    TameList16:1109 真证后可消费）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字对齐消费点）───────────────────────────
  │ ① HOL `l'y L r x = y`（命名 y）+ `LAST p ≠ y`；Lean 直接具体项
  │    `p.getLast! ≠ lYSpine L r x`（`LAST` ↦ `getLast!`，消费点同）。
  │ ② 同①：`LAST p ≠ z` ↦ `p.getLast! ≠ lZSpine L N r x`。
  │ ③ HOL `~(MEM (LAST p) (betwn r z y))` ↦
  │    `p.getLast! ∉ between r (lZSpine…) (lYSpine…)`。
  │ ④ HOL `~(MEM (LAST p) (APPEND [z] (APPEND (betwn r z y) [y])))`
  │    ↦ 同形右结合 `[z] ++ (between r z y ++ [y])`（AQ12 消费点用
  │    MEM_APPEND 拆，结合方向不敏感）。
  │ ⑤ `marked_list` 的 good_list/good_list_nodes 槽 ↦ 显式 `hL`/`hgn`；
  │    `all uniq L` 由 `hm.1.1` + `isRestrictedAllUniq` 内部导出。
  │ ⑥ `AQ_normal_list` 条件槽：`AQ1…AQ5` ↦ 显式 `aq1Concl…aq5Concl`
  │    入参（塔齐后 `transformAssumptionOfAq` 自动消去）。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（not_betwn，HOL 逐句）──────────────────────────────────
  │ 分支 LAST = y 撞 not_y；否则 `indexfBetwnEq` 给
  │ `indexf z LAST r < indexf z y r`，`indexfAddBetwn` 给
  │ `indexf z LAST r + indexf LAST y r = indexf z y r` ⇒
  │ `indexf LAST y r ≤ indexf z y r`；两条 `indexfAntisym` 反推
  │ `indexf y z r ≤ indexf y LAST r`；`indexfEqInParts`（W0）+ `idxOfGetLast`
  │ + `indexfAddLeft` 得 `idxOf y p + indexf y z r < p.length`；
  │ `indexfN` + `nextElPartsPower` + `memPowerNextEl` 把 z 拉进 p；
  │ `partsFst` 两侧同首点撞 `aq8w1_fstYNeFstZ`（QRDYXYJ_list 的
  │ FST 分量，经 markedTranslate 供 IsMarked/非 final 证人）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件前缀见命名节，私件 `aq8w1_`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W05
import Kepler.Text.TameSpine.JcajyduAqLeaf8W0
import Kepler.Text.TameSpine.TameList18
import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameSpine.JcajyduAqTowerBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 私件：getLast! 成员 / FST y ≠ FST z（QRDYXYJ_list 分量） -/

/-- `s ≠ [] ⇒ s.getLast! ∈ s`（TowerE2 `getLastMem'` 同证重推导，
per-file-private 约定零共享）。 -/
private theorem aq8w1_getLastMem {α : Type} [Inhabited α] {s : List α}
    (h : s ≠ []) : s.getLast! ∈ s := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- HOL `QRDYXYJ_list`（tame_list.hl:10307）的 FST 分量：
`~(FST (l'y L r x) = FST (l'z L N r x))`。供给 = `markedTranslate`
（TameList17:277）的 IsMarked + 非 final 证人 + `qrdyxyjList`
（TameList18:228，probe 标准三）。 -/
private theorem aq8w1_fstYNeFstZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (lYSpine L r x).1 ≠ (lZSpine L N r x).1 := by
  have hn : NormalListSpine hL N := hm.1.2.1
  have hnf := normalListNormal hL hgn hm.1.1 hn
  have htr := markedTranslate L hL hgn hunL hm hf hnf
  exact (qrdyxyjList L hL hgn hunL hm hf (hnf := hnf)
    htr.2.2.2.2.2.1 htr.2.2.2.2.2.2.1).2.2.2.2

/-! ## §1 `AQ_normal_list` 条件槽（HOL AQ8.hl:39） -/

/-- HOL `AQ_normal_list`（AQ8.hl:39）：`normal_list L (ntrans L N r x 1)`
——条件槽形，五个合取槽直接取 `aq1Concl…aq5Concl`（TowerBase），
组装顺序与 `NormalListSpine`（TameList5:127）五合取逐位相同。 -/
theorem aqs_aqNormalList (L : fgraph ℕ) (hL : GoodList L)
    (h1 : aq1Concl L hL) (h2 : aq2Concl L hL) (h3 : aq3Concl L hL)
    (h4 : aq4Concl L hL) (h5 : aq5Concl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hgn : GoodListNodesTl L hL) (hm : MarkedListSpineFull hL N r x) :
    NormalListSpine hL (ntransSpine L N r x 1) :=
  ⟨h1 N r x hgn hm, h2 N r x hgn hm, h3 N r x hgn hm, h4 N r x hgn hm,
    h5 N r x hgn hm⟩

/-! ## §2 `last_parts_y_not_y`（HOL AQ8.hl:185） -/

/-- HOL `last_parts_y_not_y`（AQ8.hl:185）：part 末元 ≠ l'y。
若相等，则 `normalListPartsNextLast` 给 `nextEl r (LAST p) = fList L (LAST p)`，
与 `nextRNotEqF`（`nextEl r y ≠ fList L y`）矛盾。 -/
theorem aq8w1_lastPartsYNotY (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    {p : List (ℕ × ℕ)}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hp : p ∈ partsSpine L r) (hyp : lYSpine L r x ∈ p) :
    p.getLast! ≠ lYSpine L r x := by
  intro h
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hnl : nextEl r p.getLast! = fList L p.getLast! :=
    normalListPartsNextLast L hL hm.1.2.1 hm.1.2.2.1 hp
  rw [h] at hnl
  exact nextRNotEqF L hL hgn hunL hm hf hnl

/-! ## §3 `last_parts_y_not_z`（HOL AQ8.hl:227） -/

/-- HOL `last_parts_y_not_z`（AQ8.hl:227）：part 末元 ≠ l'z。
若相等，`partsFst` 给 `(y).1 = (LAST p).1 = (HD p).1`，撞
`aq8w1_fstYNeFstZ`（HOL QRDYXYJ_list 的 FST 分量）。 -/
theorem aq8w1_lastPartsYNotZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    {p : List (ℕ × ℕ)}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hp : p ∈ partsSpine L r) (hyp : lYSpine L r x ∈ p) :
    p.getLast! ≠ lZSpine L N r x := by
  intro h
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hn : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hrN
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hlastmem : p.getLast! ∈ p := aq8w1_getLastMem hpne
  have h1 : (p.getLast!).1 = p.head!.1 := partsFst L hL hn hrN hp hlastmem
  have h2 : (lYSpine L r x).1 = p.head!.1 := partsFst L hL hn hrN hp hyp
  have hne := aq8w1_fstYNeFstZ L hL hgn hunL hm hf
  rw [h] at h1
  exact hne (h2.trans h1.symm)

/-! ## §4 `last_parts_y_not_betwn`（HOL AQ8.hl:296）

`LAST p ∉ betwn r z y`：HOL 证体的 indexf 算术链逐句镜像（见头注路线）。 -/
theorem aq8w1_lastPartsYNotBetwn (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    {p : List (ℕ × ℕ)}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hp : p ∈ partsSpine L r) (hyp : lYSpine L r x ∈ p) :
    p.getLast! ∉ between r (lZSpine L N r x) (lYSpine L r x) := by
  intro hmem
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hn : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hrN
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hpun : p.Nodup := partsUniq L hr1 hr2 p hp
  have hyz : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hzy : lZSpine L N r x ≠ lYSpine L r x := hyz.symm
  have hneLastZ : lZSpine L N r x ≠ p.getLast! := fun h =>
    aq8w1_lastPartsYNotZ L hL hgn hm hf hp hyp h.symm
  have hzr : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hf
  have hyr : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hf
  -- 分支 LAST = y 直接撞 not_y
  by_cases hlasty : p.getLast! = lYSpine L r x
  · exact aq8w1_lastPartsYNotY L hL hgn hm hf hp hyp hlasty
  -- indexf 算术链（HOL 逐句）
  have hlt1 : indexf (lZSpine L N r x) (p.getLast!) r <
      indexf (lZSpine L N r x) (lYSpine L r x) r :=
    ((indexfBetwnEq hzy hr1 hzr hyr).mp hmem).2
  have hadd := indexfAddBetwn hzy hr1 hzr hmem hyr
  have hkle : indexf (p.getLast!) (lYSpine L r x) r ≤
      indexf (lZSpine L N r x) (lYSpine L r x) r := by omega
  have hlastr : p.getLast! ∈ r := betwnMem hmem
  have hanti1 := indexfAntisym hlastr hyr hlasty
  have hanti2 := indexfAntisym hzr hyr hzy
  have hle2 : indexf (lYSpine L r x) (lZSpine L N r x) r ≤
      indexf (lYSpine L r x) (p.getLast!) r := by omega
  -- 归约到 p 内的索引：indexf y z r 使 y 走回 z
  have hidxY : indexf p.head! (lYSpine L r x) r = p.idxOf (lYSpine L r x) :=
    indexfEqInParts L hn hrN hyp hp
  have hidxLast : indexf p.head! (p.getLast!) r = p.idxOf (p.getLast!) :=
    indexfEqInParts L hn hrN (aq8w1_getLastMem hpne) hp
  have hidxLast2 : p.idxOf (p.getLast!) = p.length - 1 := idxOfGetLast hpun hpne
  have hylt : p.idxOf (lYSpine L r x) < p.length :=
    List.idxOf_lt_length_iff.mpr hyp
  have hheadmem : p.head! ∈ p := List.head!_mem_self hpne
  have hheadr : p.head! ∈ r := memPartsImp L hr1 hr2 hp p.head! hheadmem
  have hyle : indexf p.head! (lYSpine L r x) r ≤ indexf p.head! (p.getLast!) r := by
    rw [hidxY, hidxLast, hidxLast2]
    omega
  have haddleft := indexfAddLeft hheadr hyr hlastr hyle
  have hsum : p.idxOf (lYSpine L r x) +
      indexf (lYSpine L r x) (p.getLast!) r = p.length - 1 := by
    rw [← hidxY, haddleft, hidxLast, hidxLast2]
  have hltk : p.idxOf (lYSpine L r x) +
      indexf (lYSpine L r x) (lZSpine L N r x) r < p.length := by omega
  have hpower := nextElPartsPower L hr1 hr2 hp hyp
    (indexf (lYSpine L r x) (lZSpine L N r x) r) hltk
  have hnextn : (nextEl r)^[indexf (lYSpine L r x) (lZSpine L N r x) r]
      (lYSpine L r x) = lZSpine L N r x := indexfN hyr hzr hr1
  have hinp : (nextEl p)^[indexf (lYSpine L r x) (lZSpine L N r x) r]
      (lYSpine L r x) ∈ p := memPowerNextEl hyp _
  have hzmem : lZSpine L N r x ∈ p := by
    have h := hinp
    rw [← hpower, hnextn] at h
    exact h
  have hfst1 : (lYSpine L r x).1 = p.head!.1 := partsFst L hL hn hrN hp hyp
  have hfst2 : (lZSpine L N r x).1 = p.head!.1 := partsFst L hL hn hrN hp hzmem
  exact aq8w1_fstYNeFstZ L hL hgn hunL hm hf (hfst1.trans hfst2.symm)

/-! ## §5 `last_parts_y_not_cat`（HOL AQ8.hl:373） -/

/-- HOL `last_parts_y_not_cat`（AQ8.hl:373）：part 末元不在
`[z] ++ (betwn r z y ++ [y])`——由 not_z / not_betwn / not_y 三件
经 MEM_APPEND 分解直收。 -/
theorem aqs_lastPartsYNotCat (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    {p : List (ℕ × ℕ)}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hp : p ∈ partsSpine L r) (hyp : lYSpine L r x ∈ p) :
    p.getLast! ∉ [lZSpine L N r x] ++
      (between r (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x]) := by
  intro hmem
  rcases List.mem_append.mp hmem with h1 | h1
  · rw [List.mem_singleton] at h1
    exact aq8w1_lastPartsYNotZ L hL hgn hm hf hp hyp h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · exact aq8w1_lastPartsYNotBetwn L hL hgn hm hf hp hyp h2
    · rw [List.mem_singleton] at h2
      exact aq8w1_lastPartsYNotY L hL hgn hm hf hp hyp h2

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：五件全标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aqs_aqNormalList
#print axioms Kepler.Text.TameSpine.aq8w1_lastPartsYNotY
#print axioms Kepler.Text.TameSpine.aq8w1_lastPartsYNotZ
#print axioms Kepler.Text.TameSpine.aq8w1_lastPartsYNotBetwn
#print axioms Kepler.Text.TameSpine.aqs_lastPartsYNotCat
