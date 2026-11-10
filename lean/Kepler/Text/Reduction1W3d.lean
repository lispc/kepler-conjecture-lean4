/-
  Kepler.Text.Reduction1W3d — J4 战役 Wave W3d（首光）：HOL
  `bounded_size_finals`（`reduction1.hl:2886-:2957`）与
  `max_finals_g_exists`（`reduction1.hl:3561-:3727`）的 Lean 件，
  外加 W3 §0 的两件共享小件。

  ┌─ 件目（四处 HOL 锚）───────────────────────────────────────────
  │ §0-1 `cardSetOfListUniq`  ← `ssreflect/seq2-compiled.hl:953`
  │      `uniq l ==> CARD (set_of_list l) = sizel l`
  │      树内 `TameSpine.TameList19:412 cardSetOfListUniq2` 是**逆命题**
  │      （`ncard = length → Nodup`），不覆盖本向 ⇒ 真缺件（~8 行）。
  │ §0-2 `mapInjInUniq`      ← `ssreflect/seq-compiled.hl:3135`
  │      **已在库**：`TameLp.la7_nodup_map_on`（TameLp:5329），
  │      `TameList40:55` 已记档等价 ⇒ 本件为零语义别名（1 行），不重造。
  │ §1   `normalListFlattenBound` + `boundedSizeFinals`
  │      ← `reduction1.hl:2886-:2957`
  │ §2   `FinalsAdmissible` + `maxFinalsGExists`
  │      ← `reduction1.hl:3561-:3727`
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（重写记账，非逐行直译）─────────────────────────────────
  │ HOL `bounded_size_finals` 走
  │   `sizel (finals g) ≤ CARD (set_of_list (undup (filter (final_list L') N')))`
  │   `≤ sizel (filter (final_list L') N') ≤ sizel N' ≤ sizel (list_of_darts L)`
  │ 的 CARD/undup 三段链，其第一段 `sizel (finals g) = CARD (set_of_list (MAP
  │ (list_pairs o FST) (filter SND (faces g))))` 需要 MAP 后 uniq（= HOL 的
  │ `good_list_uniq` + `map_inj_in_uniq` + `list_pairs_inj` 三件套，而
  │ `good_list (quotient_list L' N')` 侧在 Lean 只有 `quotientListSpine`
  │ 载体、与链侧 `quotientList` 无桥）。
  │ **本件改走 faces 计数链**（同一上界、更短、零新桥）：
  │   `(finals g).length ≤ g.faces.length`                 [filter]
  │   `= (fgraphOfGraph g).length`                          [length_map]
  │   `= (quotientList L' N').length`                       [matchQuotientList 第 2 合取]
  │   `= N'.length`                                         [coreList/quotientList 都是 map]
  │   `≤ N'.flatten.length`                                 [normalList 合取 2 各行非空]
  │   `≤ (listOfDarts L').length`                           [合取 1 Nodup + 合取 3/4 出 dart]
  │   `= (listOfDarts L).length`                            [iso + injOnListOfDarts]
  │ 该链**不消费** `list_pairs_inj` / `good_list_uniq` / `map_inj_in_uniq`，
  │ 因此 §0-2 在本件里只作为下游可用别名交付、不被 `boundedSizeFinals` 调用。
  └────────────────────────────────────────────────────────────────

  ┌─ `maxFinalsGExists` 的形状（与 HOL 唯一差异：种子槽显式化）──────
  │ HOL 证体：造集合 `S = IMAGE (sizel ∘ finals) {候选三元组}`，
  │ `NUM_FINITE_IMP_MAX_EXISTS` 取最大元，再反解极值性质。两半：
  │   (a) `FINITE S`  ← `bounded_size_finals`（本文件 §1，已真证）；
  │   (b) `S ≠ {}`     ← **种子三元组**：HOL 用 `foldr_maxn_exists` +
  │       `UYOUIXG`（:2402，160 行）+ `flag_list_seed`（:3358，203 行）
  │       + `seed_finals`/`seed_planegraphP`/`seed_size_v_gt_1` 造出
  │       `(Seed p, L', N')`。这些件属 **W2/W3c**，本波未落 ⇒
  │       `hne : ∃ …, FinalsAdmissible …` 立为**显式槽**（与
  │       `JcajyduShell` 的 `hp` 槽、`JcajyduRed5Top` 的 `hF` 槽同款），
  │       (a)+(极值反解) 全部真证。W3c 落 `UYOUIXG`/`flag_list_seed`
  │       后本件即无条件形，陈述与证体**零改动**（只喂 `hne`）。
  └────────────────────────────────────────────────────────────────

  ┌─ 逐槽对照（HOL → Lean；DIFFERS 全表）──────────────────────────
  │ ① `sizel`            ↦ `List.length`（树内无 `sizel` 名）
  │ ② `foldr maxn 0`     ↦ `List.foldr max 0`
  │ ③ `final_list L' r`  ↦ `Reduction5.finalList L' r`（ChainLists 侧同体）
  │ ④ `all uniq (quotient_list L' N')`
  │                      ↦ `∀ r ∈ quotientList L' N', r.Nodup`
  │ ⑤ `all (\v. sizel (filter (MEM v) q) > 1) (flatten q)`
  │                      ↦ `∀ v ∈ q.flatten, 1 < (q.filter (fun r => decide (v ∈ r))).length`
  │ ⑥ `iso_list (L,[]) (L',[])` ↦ `IsoListSpine L L' [] []`（4 参平铺，
  │    HOL 把 `(L,N)` 捆成单参；载体分歧 TameList1:71 已记档）
  │ ⑦ `planegraphP p g`  ↦ `TameSpine.PlaneGraphPSpine p g`（TameList58:170，
  │    HOL 形；**不是** AFP 的 `Graphs.PlaneGraphsP`，后者多 `∧ g.final`）
  │ ⑧ `vertices_set2 g = elements_of_list (fgraph g)`
  │                      ↦ `TameCorrList.VerticesSet2Eq g`（TameCorrList:84 同体）
  │ ⑨ `good_faces_v3 g`  ↦ `TameCorrList.GoodFacesV3 g`（:80）
  │ ⑩ `normal_list L' N'`↦ `ChainLists.normalList L' hL' N'`（**依赖式**：
  │    `hL' : GoodList L'` 显式参数，HOL 无依赖；DIFFERS-② 同 `TameLp`
  │    系列先例）
  │ ⑪ `~(N' = [])`       ↦ `N' ≠ []`
  │ ⑫ `flag_list L' N'`  ↦ `ChainLists.flagList L' N'`
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改任何既有陈述/定义；
  新增 def 仅 `FinalsAdmissible` 一枚（纯 HOL 十合取块缩写，零证明义务，
  先例 = `JcajyduShell` 三 `def : Prop` 槽，`0c520618`）。
  **显式禁搬的 HOL 死码**（本文件零引用）：`containsDuplicateEdge`
  （:1149-:1162 整块注释）、`oldvertex2`（:1767 死件）、`SHXWXQ`
  （:2335 别名）、`not_containsDuplicateEdge_iota` / `iota_generatePolygon`
  （:3763-:3798 整块注释）。
-/

import Kepler.Text.TameSpine.TameList57
import Kepler.Text.TameSpine.TameList58
import Kepler.Text.TameSpine.TameList19
import Kepler.Text.TameCorrList
import Kepler.Text.ChainListsL2
import Kepler.Text.Reduction3DefsLayer

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList listOfDarts listPairs)
open Kepler.Graphs (fgraph Graph Face finals)
open Kepler.Text.Reduction5 (Dart quotientList)
open Kepler.Text.ChainLists (normalList flagList loopList)
open Kepler.Text.Reduction3 (matchQuotientList fgraphOfGraph)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq GoodListNodes)
open Kepler.Text.TameSpine (PlaneGraphPSpine injOnListOfDarts IsoListSpine)
open Kepler.Text.TameLp (elementsOfList hypermapOfList)

/-! ## §0 两件共享小件（W3 §0 / W1 共用） -/

/-- **HOL `card_set_of_list_uniq`**（`ssreflect/seq2-compiled.hl:953`
`uniq l ==> CARD (set_of_list l) = sizel l`）的泛型 `toFinset` 形。

树内 `TameSpine.TameList19:412 cardSetOfListUniq2` 是**逆命题**
（`ncard = length → Nodup`），本向为零命中 ⇒ 真缺件。载体：
`set_of_list l` ↦ `(l.toFinset : Set α)`（`toFinset` 的 Set 强制即
`{x | x ∈ l}`，`List.mem_toFinset` 定义性）；`CARD` ↦ `Set.ncard`。 -/
theorem cardToFinsetOfNodup {α : Type*} [DecidableEq α] {l : List α}
    (h : l.Nodup) : (l.toFinset : Set α).ncard = l.length := by
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup h]

/-- **HOL `card_set_of_list_uniq`**（`seq2-compiled.hl:953`）在树内
ℕ 载体 `setOfListNatSpine`（`TameList19:201`，`{x | x ∈ l}`）上的
逐槽形——J4 后半 `CARD (set_of_list …)` 站点直接可用的 HOL 同名族。 -/
theorem cardSetOfListUniq {l : List ℕ} (h : l.Nodup) :
    (Kepler.Text.TameSpine.setOfListNatSpine l).ncard = l.length := by
  have hcoe : Kepler.Text.TameSpine.setOfListNatSpine l = (l.toFinset : Set ℕ) := by
    ext x
    simp [Kepler.Text.TameSpine.setOfListNatSpine]
  rw [hcoe, cardToFinsetOfNodup h]

/-- **HOL `Seq.map_inj_in_uniq`**（`ssreflect/seq-compiled.hl:3135`）
`(!x y. MEM x l /\ MEM y l /\ f x = f y ==> x = y) /\ uniq l ==>
uniq (MAP f l)`。

**不重造**：本体已是 `TameLp.la7_nodup_map_on`（TameLp:5329），
`TameList40:55` 已记档「`Seq.map_inj_in_uniq` = `la7_nodup_map_on`」。
本件为零语义别名（让下游按 HOL 名检索，避免第二次考古）。 -/
theorem mapInjInUniq {α β : Type*} {f : α → β} {l : List α}
    (hinj : ∀ u ∈ l, ∀ v ∈ l, f u = f v → u = v) (hn : l.Nodup) :
    (l.map f).Nodup :=
  Kepler.Text.TameLp.la7_nodup_map_on hinj hn

/-! ## §1 `bounded_size_finals`（reduction1.hl:2886-:2957） -/

/-- HOL `normal_list_size_bound`（`tame_list.hl:12633`
`!L N. normal_list L N ==> sizel N <= sizel (list_of_darts L)`）在
**链侧载体** `normalList` 上的重证。

为什么重推而不复用 `TameSpine.normalListSizeBound`（TameList45:170）：
后者吃 `NormalListSpine`（TameList5:127），与链侧 `normalList`
（ChainListsL1:89）是**不同常量**（`fLast`/`loopList` vs
`fLastSpine`/`loopListSpine`，`hypermapOfList` 同载体），树内无
`normalList → NormalListSpine` 桥（`ChainBridgeParts` 只有
`parts`/`quotientList`/`flagList`/`sFlagList`/`markedList` 五条 iff）。
本件按 HOL 同一数学（`sumn_size` + `uniq_leq_size` 两段）在链侧重推，
14 行；不新增桥、不改既有件。 -/
theorem normalListFlattenBound {L : fgraph ℕ} {hL : GoodList L}
    {N : List (List Dart)} (hn : normalList L hL N) :
    N.length ≤ (listOfDarts L).length := by
  -- 第 1 段：N.length ≤ N.flatten.length（各行非空）
  have h1 : N.length ≤ N.flatten.length := by
    have hpt : ∀ m ∈ N.map List.length, 1 ≤ m := by
      intro m hm
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
      have hne : s ≠ [] := hn.2.1 s hs
      have hpos : 0 < s.length := List.length_pos_iff.mpr hne
      omega
    calc N.length = (N.map List.length).length := (List.length_map _).symm
      _ ≤ (N.map List.length).sum := List.length_le_sum_of_one_le _ hpt
      _ = N.flatten.length := (List.length_flatten).symm
  -- 第 2 段：N.flatten ⊆ list_of_darts L（合取 3/4 的 loopList 槽出 dart）
  have h2 : ∀ x ∈ N.flatten, x ∈ listOfDarts L := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := List.mem_flatten.mp hx
    exact (hn.2.2.2.1 s hs x hxs).1
  exact h1.trans (List.Subperm.length_le (List.subperm_of_subset hn.1 h2))

/-- **HOL `bounded_size_finals`**（`reduction1.hl:2886-:2957`）逐槽折算：
`∃ n, ∀ g L' N'. iso_list (L,[]) (L',[]) /\ normal_list L' N' /\
match_quotient_list g L' N' ==> sizel (finals g) <= n`，见证
`n = sizel (list_of_darts L)`（与 HOL 同一见证，逐字）。

证明路线见文件头「路线」段：faces 计数链，零新桥。
HOL 前提 `good_list_nodes L` / `is_restricted (hypermap_of_list L)`
在本路线中**未被消费**（HOL 侧亦仅在 `good_list L'` 的运输间接用到），
按原文保留（`_hgn`/`_hres`）——「冗余前提逐字保留」体例，
先例 = `TameList57.injOnListOfDarts` 的 `_hinj`。 -/
theorem boundedSizeFinals (L : fgraph ℕ) (hL : GoodList L)
    (_hgn : GoodListNodes L)
    (_hres : (hypermapOfList L hL).IsRestricted) :
    ∃ n, ∀ (g : Graph) (L' : fgraph ℕ) (hL' : GoodList L')
      (N' : List (List Dart)),
      IsoListSpine L L' [] [] → normalList L' hL' N' →
      matchQuotientList g L' N' → (finals g).length ≤ n := by
  refine ⟨(listOfDarts L).length, ?_⟩
  intro g L' hL' N' hiso hn hm
  -- (1) finals ⊆ faces
  have h1 : (finals g).length ≤ g.faces.length :=
    List.length_filter_le Face.final g.faces
  -- (2) g.faces.length = N'.length（matchQuotientList 第 2 合取 + 双 map）
  have h2 : g.faces.length = N'.length := by
    have e1 : g.faces.length = (fgraphOfGraph g).length := by
      simp [fgraphOfGraph]
    rw [e1, hm.2]
    simp [Kepler.Text.Reduction5.quotientList, Kepler.Text.Reduction5.coreList]
  -- (3) N'.length ≤ (listOfDarts L').length（normal_list_size_bound 链侧形）
  have h3 : N'.length ≤ (listOfDarts L').length := normalListFlattenBound hn
  -- (4) iso 保 list_of_darts 长度
  have h4 : (listOfDarts L').length = (listOfDarts L).length := by
    obtain ⟨phi, hinj, hL'eq, -⟩ := hiso
    rw [hL'eq, injOnListOfDarts L phi hinj, List.length_map]
  omega

/-! ## §2 `max_finals_g_exists`（reduction1.hl:3561-:3727） -/

/-- 候选三元组谓词 —— HOL `max_finals_g_exists` 陈述里的**十合取块**
（`reduction1.hl:3567-:3577` 与 `:3579-:3589` 两处逐字同体）的命名缩写。

**纯缩写 `def : Prop`**（零证明义务；`#print` 即见 HOL 十合取，逐槽对照
见文件头 DIFFERS 表）。先例 = `JcajyduShell.restrictedHypermapsArePlaneGraphsV4`
（`0c520618`）等三枚陈述槽。 -/
def FinalsAdmissible (L : fgraph ℕ) (p : ℕ) (g : Graph)
    (L' : fgraph ℕ) (hL' : GoodList L') (N' : List (List Dart)) : Prop :=
  matchQuotientList g L' N' ∧
  normalList L' hL' N' ∧
  (∀ r ∈ quotientList L' N', r.Nodup) ∧
  N' ≠ [] ∧
  IsoListSpine L L' [] [] ∧
  PlaneGraphPSpine p g ∧
  VerticesSet2Eq g ∧
  GoodFacesV3 g ∧
  flagList L' N' ∧
  (∀ v ∈ (quotientList L' N').flatten,
      1 < ((quotientList L' N').filter (fun r => decide (v ∈ r))).length)

/-- **HOL `max_finals_g_exists`**（`reduction1.hl:3561-:3727`）。

结论 = 十合取 + 极值性质（`sizel (finals g'') ≤ sizel (finals g')`），
即「极大反例原理的存在最大元那一步」。**唯一与 HOL 的差异**：HOL 用
`UYOUIXG`(:2402) + `flag_list_seed`(:3358) + 三条 `seed_*` 造出种子
三元组以证 `S ≠ {}`；这些件属 W2/W3c，尚未落库 ⇒ 本件把「候选集非空」
立为显式槽 `hne`（`FinalsAdmissible` 的 ∃-形）。`hne` 被填掉后本件
成为 `max_finals_g_exists` 的无条件形，**陈述与证体零改动**。

`FINITE S` 半边 = §1 `boundedSizeFinals`（已真证）；
极值反解半边 = `Set.exists_max_image`（core，等价于 HOL 消费的
`Rogers.NUM_FINITE_IMP_MAX_EXISTS`，后者在树内 `PackingAuto7:3798`，
但本件**不 import** 它——那条 import 会把整个 Packing 闭包拉进来，
而 `Set.exists_max_image` 是它的逐字核心）。 -/
theorem maxFinalsGExists (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodes L) (hres : (hypermapOfList L hL).IsRestricted)
    (p : ℕ) (_hp : p = (L.map List.length).foldr max 0 - 3)
    (hne : ∃ (g : Graph) (L' : fgraph ℕ) (hL' : GoodList L')
        (N' : List (List Dart)), FinalsAdmissible L p g L' hL' N') :
    ∃ (g' : Graph) (L' : fgraph ℕ) (hL' : GoodList L')
      (N' : List (List Dart)),
      FinalsAdmissible L p g' L' hL' N' ∧
      (∀ (g'' : Graph) (L'' : fgraph ℕ) (hL'' : GoodList L'')
        (N'' : List (List Dart)),
        FinalsAdmissible L p g'' L'' hL'' N'' →
        (finals g'').length ≤ (finals g').length) := by
  classical
  obtain ⟨n, hn⟩ := boundedSizeFinals L hL hgn hres
  let S : Set ℕ := {m | ∃ (g : Graph) (L' : fgraph ℕ) (hL' : GoodList L')
      (N' : List (List Dart)), FinalsAdmissible L p g L' hL' N' ∧
      m = (finals g).length}
  have hSfin : S.Finite := by
    refine Set.Finite.subset (Set.finite_Icc 0 n) ?_
    intro m hm
    dsimp only [S] at hm
    obtain ⟨g, L', hL', N', hadm, rfl⟩ := hm
    exact ⟨Nat.zero_le _, hn g L' hL' N'
      hadm.2.2.2.2.1 hadm.2.1 hadm.1⟩
  have hSne : S.Nonempty := by
    obtain ⟨g, L', hL', N', hadm⟩ := hne
    exact ⟨(finals g).length, g, L', hL', N', hadm, rfl⟩
  obtain ⟨m, hmS, hmax⟩ := Set.exists_max_image S id hSfin hSne
  dsimp only [S] at hmS
  obtain ⟨g', L', hL', N', hadm', hmEq⟩ := hmS
  refine ⟨g', L', hL', N', hadm', ?_⟩
  intro g'' L'' hL'' N'' hadm''
  have hmem : (finals g'').length ∈ S := ⟨g'', L'', hL'', N'', hadm'', rfl⟩
  have hle : (finals g'').length ≤ m := hmax _ hmem
  omega

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；四件预期 ⊆ 标准三 `[propext, Classical.choice,
Quot.sound]`、零未证公理）。落库时编排者可整体注释本节，不影响任何声明。 -/
#print axioms Kepler.Text.Reduction1.cardToFinsetOfNodup
#print axioms Kepler.Text.Reduction1.cardSetOfListUniq
#print axioms Kepler.Text.Reduction1.mapInjInUniq
#print axioms Kepler.Text.Reduction1.normalListFlattenBound
#print axioms Kepler.Text.Reduction1.boundedSizeFinals
#print axioms Kepler.Text.Reduction1.maxFinalsGExists
