/-
  Kepler.Text.TameSpine.JcajyduShell — jcajydu-c1 壳波：HOL `Jcajydu.JCAJYDU`
  （JCAJYDU.hl:51-90，num 版）与 `Jcajydu.JCAJYDU1`（:23-48，type-A 版）的
  **条件形壳定理**，Assembly-free 私模块。

  ┌─ 靶与分层（SCOUT.md §1/§6-C1）────────────────────────────────
  │ `Assembly.lean:2509`（grep 锚 `theorem jcajydu`）的 inline `sorry`
  │ 是无条件形占位；本模块按 Assembly:2506 注记「填证时按 HOL 原形拆回」
  │ 把孪生落成条件形：前提 = `restricted_hypermaps_are_planegraphs_v4`
  │ （tame_defs2.hl:693 具名 def；reduction5.hl:150 真证定理）。
  │ 前提槽落成 `def … : Prop := …` 纯定义（零证明义务、零 axiom、零
  │ sorry）；填证 = J 战役 reduction1-5 链（SCOUT §2，≈20k HOL 行）。
  └────────────────────────────────────────────────────────────────

  ┌─ 层间勘误（与 SCOUT §4「前置全部已就位」的出入；机器证据为准）──
  │ RXOKSKC（TameList69:605）产出在 **Set α 层**
  │ （`L : List (List (Set α))`，`hypermapOfListG` 泛型层），而 num 编码件
  │ JXBJOAB（TameList1:175）按 honest-narrowing 记档收窄为 **ℕ→ℕ 单态**
  │ （id 重标号即证人），iso_list/GNBEVVU 全族亦 ℕ 单态。HOL 壳证明
  │ （JCAJYDU.hl:57 `INTRO_TAC JXBJOAB`）消费的恰是 JXBJOAB 的**跨型**
  │ 内容（`(A->bool)list → num list`，INJ_NUM_EXISTS），树内零命中
  │ （grep 实证，见 DELIVERY）。故「无条件缺桥的 premise 壳」在本树
  │ 不可闭合；缺口立为显式槽 `rxNumTransport`（只立陈述）。
  │ 本模块交付：两陈述槽 + 一桥槽（纯 def）+ 三条真证壳定理
  │ （jcajydu1Shell / jcajyduShell / Set 层归约胶水）。
  └────────────────────────────────────────────────────────────────

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ import = `TameList69`（RXOKSKC + rx 词表）+ `TameList1`（DAKEFCC）+
  │ `TameCorrList`（GoodGraphV4/GoodListNodes 镜像）。闭包零
  │ `Kepler.Assembly` 主模块（GoodList 经 `Kepler.Assembly.GoodListDefs`，
  │ P6-C 设计的非环底座；grep 闭包无 `^import Kepler.Assembly$`）。
  │ 环自检（logs/ring_check.log）：独立探针只 import 本模块三依赖后
  │ `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │ 必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  ┌─ 与 Assembly 消费面的三桥记账（J5 wrapper 折算，均平凡）────────
  │ ① `TameCorrList.GoodGraphV4` ↔ `Assembly.GoodGraphV4`（:2303）体逐字
  │   同体 defeq（Assembly:2521 wrapper `exact` 直通先证）；
  │ ② `H.Iso H'` ↔ `HypermapIso H H'`（Hypermap.lean:8249 / Assembly.lean:192
  │   展开同体 defeq）；
  │ ③ `IsHypermapOfListTl ↔ Assembly.IsHypermapOfList`（:210）四字段匿名
  │   构造器各一行（Assembly:2521 同款：`⟨darts_eq, edgeMap_eq, nodeMap_eq,
  │   faceMap_eq⟩`）。
  │ J5 装配形：`Assembly.jcajydu H hres := jcajyduShell reduction5孪生
  │ 跨型桥 H hres`，结论槽按 ①②③ 折算即 Assembly 原签名
  │ （textCapstone :7197 `obtain ⟨g, hgPlane, hgg4, Hg, hHgIs, hIsoFanHg⟩ :=
  │   jcajydu _ hresH` 消费形状零改动）。
  └────────────────────────────────────────────────────────────────

  **纪律**：无 axiom/sorry/admit/native_decide；不改既有陈述；
  主仓 tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.TameList69
import Kepler.Text.TameSpine.TameList1
import Kepler.Text.TameCorrList

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Text (Hypermap)
open Kepler.Graphs
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (hypermapOfList IsHypermapOfListTl hypermapOfList_isHypermapOfListTl)
open Kepler.Text.TameCorrList (GoodGraphV4 GoodListNodes)

/-! ## §1 陈述槽（纯 `def … : Prop`，零证明义务；填证属 J 战役） -/

/-- **num 层前提槽**（本波主交付的 `hp`）：HOL `restricted_hypermaps_are_planegraphs_v4`
（tame_defs2.hl:693 具名 def；JCAJYDU.hl:51-56 前提；reduction5.hl:150 真证定理
`restricted_hypermaps_are_planegraphs_thm` = `MATCH_MP_TAC Reduction3.reduction_F;
REWRITE_TAC[assumption_setK10]`）的 Lean 孪生。HOL 原句逐槽对照：

```
!Ln:(num list)list. good_list Ln /\ good_list_nodes Ln /\
  is_restricted (hypermap_of_list Ln) ==>
  (?gn. PlaneGraphs gn /\ good_graph_v4 gn /\
     iso (hypermap_of_list Ln) (hypermap_of_list (fgraph gn)))
```

折算：`good_list Ln` ↦ `GoodList Ln`（Kepler.Assembly.GoodListDefs，
list_hypermap-compiled.hl:63 逐句镜像）；`good_list_nodes Ln` ↦
`GoodListNodes Ln`（TameCorrList 镜像 = Assembly:2297 同体，∀hL 内量化保
arity）；`hypermap_of_list Ln` ↦ `hypermapOfList Ln hg`（TameLp:5188 构造，
依赖 GoodList 见证 hg，与 Assembly 依赖式折算一致）；`PlaneGraphs` ↦
`Kepler.Graphs.PlaneGraphs`（Plane1.thy 港口）；`good_graph_v4` ↦
`GoodGraphV4`（TameCorrList 镜像，tame_defs2.hl:56-63 六合取）；结论 iso 的
右见证 `hypermap_of_list (fgraph gn)` ↦ `∃ hg' : GoodList gn.fgraph`（取自
`GoodGraphV4 gn` 首槽的冗余显式化）。**只立陈述**。 -/
def restrictedHypermapsArePlaneGraphsV4 : Prop :=
  ∀ (Ln : fgraph ℕ) (hg : GoodList Ln), GoodListNodes Ln →
    (hypermapOfList Ln hg).IsRestricted →
    ∃ gn : Graph, PlaneGraphs gn ∧ GoodGraphV4 gn ∧
      ∃ hg' : GoodList gn.fgraph,
        (hypermapOfList Ln hg).Iso (hypermapOfList gn.fgraph hg')

/-- **Set α 层前提槽**：HOL `Jcajydu.JCAJYDU1`（JCAJYDU.hl:23-29 前提）的
Lean 孪生，取 RXOKSKC 的实际产出层（`hypermap_of_list` 泛型 α 层 = TameSpine
rx 词表：`rxGoodList` TameList66:539 / `rxGoodListNodes` TameList67:376 /
`hypermapOfListG` TameList67:291）。`good_list L` ↦ `rxGoodList L`；
`good_list_nodes L` ↦ `rxGoodListNodes L hL`（构造条件化的依赖形，
TameList67 头注记档）；`is_restricted` / `iso` 槽同上（`Hypermap.IsRestricted`
Hypermap.lean:9645 / `Hypermap.Iso` :8249）。**只立陈述**。 -/
def restrictedHypermapsArePlaneGraphsV4Set (α : Type*) [DecidableEq α] : Prop :=
  ∀ (L : List (List (Set α))) (hL : rxGoodList L) (hgn : rxGoodListNodes L hL),
    (hypermapOfListG L hL).IsRestricted →
    ∃ gn : Graph, PlaneGraphs gn ∧ GoodGraphV4 gn ∧
      ∃ hg' : GoodList gn.fgraph,
        (hypermapOfListG L hL).Iso (hypermapOfList gn.fgraph hg')

/-- **跨型桥槽**（J 战役缺口件，**只立陈述**）：Set α 层受限 list 表示可
编码为 num 层 list 表示，iso 与 nodeSet 语义同时保持。内容 = HOL 壳证明
（JCAJYDU.hl:57-73）里四件的 **Set α → ℕ 跨型版**打包：
`JXBJOAB`（tame_list.hl:3733，INJ_NUM_EXISTS 有限集 num 编码）+
`iso_list_good_list`（:3554）+ `iso_list_good_list_nodes` + `GNBEVVU`
（:3540，`hypermap_of_list_map`）。树内 iso_list 族全部 ℕ→ℕ 单态
（TameList1:169 honest-narrowing 记档），跨型版零移植。
两个假设槽按 RXOKSKC 全量供给写（填桥者可用上下文即此；`hgn` 供
iso_list_good_list_nodes 内容的 nodeSet 侧义务）。 -/
def rxNumTransport (α : Type*) [DecidableEq α] : Prop :=
  ∀ (L : List (List (Set α))) (hL : rxGoodList L) (hgn : rxGoodListNodes L hL),
    ∃ (Ln : fgraph ℕ) (hg : GoodList Ln) (hgnN : GoodListNodes Ln),
      (hypermapOfListG L hL).Iso (hypermapOfList Ln hg)

/-! ## §2 壳定理（真证；HOL tactic 逐步对照见各注） -/

/-- **HOL `Jcajydu.JCAJYDU1` 的应用形**（JCAJYDU.hl:30-47）：前提吃
Set α 层槽（RXOKSKC 的产出层），结论即 Assembly `jcajydu` 结论槽的
Assembly-free 孪生（三桥 defeq，见模块头记账）。

HOL 逐步对照（JCAJYDU1.hl:30-47）：
1. `INTRO_TAC Rxokskc.RXOKSKC[H]; ASM_REWRITE_TAC`（:31-32）↦ `RXOKSKC`
   （TameList69:605；`all uniq` 槽 HOL 亦不消费，照原样携带）；
2. `ANTS_TAC; BY(ASM_MESON_TAC[Tame_list.DAKEFCC])`（:38-43）↦ 喂前提所需
   `is_restricted (hypermap_of_list L)` 由 `DAKEFCC`（= iso_restricted 别名，
   TameList1:631）沿 RXOKSKC 的 iso 正向运输（`Nonempty α` 从
   `IsRestricted` 首槽 dart 非空导出，HOL 类型恒非空的折算）；
3. `TYPIFY g EXISTS_TAC; ASM_REWRITE_TAC; ASM_MESON_TAC[iso_trans]`
   （:44-47）↦ `Hypermap.Iso.trans`（Hypermap.lean:8281）把「H ≅ hol L」
   （RXOKSKC）与「hol L ≅ hol (fgraph gn)」（前提结论）拼接；
   `IsHypermapOfListTl` 见证槽由构造件 `hypermapOfList_isHypermapOfListTl`
   （TameLp:6139）供出——HOL 结论直接写 `hypermap_of_list (fgraph gn)`
   本身，Lean 孪生按 Assembly 接口形状以 `∃ H'` + 规格见证表达（三桥
   记账 ③）。 -/
theorem jcajydu1Shell {α : Type*} [DecidableEq α]
    (hpSet : restrictedHypermapsArePlaneGraphsV4Set α)
    (H : Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Graph, PlaneGraphs g ∧ GoodGraphV4 g ∧
      ∃ H' : Hypermap (ℕ × ℕ), IsHypermapOfListTl g.fgraph H' ∧ H.Iso H' := by
  -- HOL :31-32（RXOKSKC 实例化）
  obtain ⟨L, hL, _huniq, hgn, hiso1⟩ := RXOKSKC H hres
  -- HOL 类型恒非空的折算：IsRestricted 首槽 dart 非空 ⇒ Nonempty α
  haveI hNE : Nonempty α := by
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hres.1
    exact ⟨x⟩
  -- HOL :38-43（DAKEFCC 正向运输：is_restricted 沿 iso1 到 hol L 侧）
  have hresL := (DAKEFCC hiso1).1 hres
  -- HOL :44-45（前提给 gn：PlaneGraphs / good_graph_v4 / iso）
  obtain ⟨gn, hpg, hgg, hg', hiso2⟩ := hpSet L hL hgn hresL
  -- HOL :46-47（iso_trans 拼接 + 规格见证收口）
  exact ⟨gn, hpg, hgg, hypermapOfList gn.fgraph hg',
    hypermapOfList_isHypermapOfListTl gn.fgraph hg', hiso1.trans hiso2⟩

/-- **层归约胶水**：num 层槽 + 跨型桥 ⇒ Set α 层槽。
即 J 战役的攻击面 = num 层 reduction 链 + 一座 `rxNumTransport` 桥，
Set 层槽自动跟随（无需独立填证）。证明：桥给出 Ln 与跨型 iso2，
`DAKEFCC` 把前提 antecedent 的 is_restricted 运输到 num 侧喂 `hp`
（HOL JCAJYDU1 内 `ANTS_TAC` 段的跨型同构段），再 `Iso.trans` 收口。 -/
theorem restrictedHypermapsArePlaneGraphsV4Set_of_num
    (hp : restrictedHypermapsArePlaneGraphsV4)
    {α : Type*} [DecidableEq α] (htx : rxNumTransport α) :
    restrictedHypermapsArePlaneGraphsV4Set α := by
  intro L hL hgn hresL
  obtain ⟨Ln, hg, hgnN, hiso2⟩ := htx L hL hgn
  haveI hNE : Nonempty (Set α × Set α) := by
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hresL.1
    exact ⟨x⟩
  have hresLn := (DAKEFCC hiso2).1 hresL
  obtain ⟨gn, hpg, hgg, hg', hiso3⟩ := hp Ln hg hgnN hresLn
  exact ⟨gn, hpg, hgg, hg', hiso2.trans hiso3⟩

/-- **HOL `Jcajydu.JCAJYDU`（JCAJYDU.hl:51-90）的应用形** —— 本波主交付：
`Assembly.lean:2509 jcajydu`（sorry 占位）的条件形孪生。签名对照：`H`/
`hres` 两参数与 Assembly 逐字同形；`hp`（num 层前提槽）与 `htx`（跨型桥槽）
为 J 战役填件，装配即 Assembly 侧删 sorry 波（SCOUT §6 方案 A/B 的 J5）。

HOL 逐步对照（JCAJYDU.hl:53-89）：`DISCH_TAC`（收 hp）→ `MATCH_MP_TAC
JCAJYDU1`（:54，复用 JCAJYDU1；其前提的 num 版经 :55-73 的 JXBJOAB +
iso_list_good_list/nodes + iso_list_restricted + GNBEVVU 折算）——本证明即
`jcajydu1Shell (Set 层槽_of_num hp htx) H hres`：跨型四件的全部内容收进
`htx`，RXOKSKC/DAKEFCC/iso_trans 在 `jcajydu1Shell` 内逐段对应。 -/
theorem jcajyduShell (hp : restrictedHypermapsArePlaneGraphsV4)
    {α : Type*} [DecidableEq α] (htx : rxNumTransport α)
    (H : Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Graph, PlaneGraphs g ∧ GoodGraphV4 g ∧
      ∃ H' : Hypermap (ℕ × ℕ), IsHypermapOfListTl g.fgraph H' ∧ H.Iso H' :=
  jcajydu1Shell (restrictedHypermapsArePlaneGraphsV4Set_of_num hp htx) H hres

end Kepler.Text.TameSpine

/-! 公理审计锚（本文件编译即执行；预期 = 标准三
`[propext, Classical.choice, Quot.sound]`，零 sorryAx——壳吃 `hp`/`htx`
参数、三陈述槽为纯 def 无证明义务。落库时编排者可整体注释本节，
不影响任何声明。） -/
#print axioms Kepler.Text.TameSpine.jcajyduShell
#print axioms Kepler.Text.TameSpine.jcajydu1Shell
#print axioms Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4Set_of_num
