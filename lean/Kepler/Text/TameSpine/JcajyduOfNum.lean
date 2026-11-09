/-
  Kepler.Text.TameSpine.JcajyduOfNum — W2.5 P3 收口件：HOL `Jcajydu.JCAJYDU`
  （JCAJYDU.hl:51-90）的忠实无条件形——消费 `rxNumTransportBridge`
  （JcajyduRxBridge:470，286cf3b6）真证消去 `jcajyduShell` 的 `htx`
  跨型桥槽，把本件前提收窄到 num 层 V4 单槽（与 HOL 前提同形）。

  ┌─ 立项与勘误（2-γ W2.5，编排者续721 派单 P1-P3）─────────────────
  │ P1/P2（双型化泛化 + rx 层 transport + nodeSet 轨道像链）已由
  │ JcajyduRxBridge §1-§4 全量在树（286cf3b6，早于基线 fde99ddd；
  │ tame-corr W2 侦察按 TameList69 命中面搜消费边漏检该模块——rxNumTransport
  │ 缺口 500-900 行定量据此作废，机器复核勘误）。本模块只交付 P3：
  │ 无条件形壳 + 文件尾公理锚。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（与 HOL JCAJYDU :51-61 原形的形状差，非语句弱化）──────
  │ ① 结论槽 = `∃ H', IsHypermapOfListTl g.fgraph H' ∧ H.Iso H'`
  │    规格见证形（P6-C 桥 + TameCorrBase 典范性折算 HOL 的
  │    `iso H (hypermap_of_list (fgraph g))`；Assembly 三桥记账同
  │    JcajyduShell 头注 ①②③）。
  │ ② 前提槽 = 依赖形：`hypermapOfList Ln hg` 携 GoodList 见证 hg、
  │    结论槽含 `∃ hg'`（HOL hypermap_of_list 全函数 vs Lean 构造
  │    条件化，JcajyduShell 头注已记档）。
  │ ③ `htx` 槽消失 = 本件增量（rxNumTransportBridge 真证供给）。
  └────────────────────────────────────────────────────────────────

  消费面：Assembly.jcajydu（:2509 占位）删 sorry 波 = 本件 + 三桥折算
  （J5 形，JcajyduShell 头注）；V4 前提槽填证 = reduction5 链（另账）。

  纪律：零 axiom/sorry/admit/native_decide；零既有陈述改动；主仓 tracked
  零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.JcajyduRxBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Text (Hypermap)
open Kepler.Graphs
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (IsHypermapOfListTl)
open Kepler.Text.TameCorrList (GoodGraphV4)

/-- **HOL `Jcajydu.JCAJYDU`（JCAJYDU.hl:51-61）忠实无条件形** —— W2.5 P3
主交付：num 层前提 `hp` 单槽供入（HOL 前提 `!Ln. good_list Ln ∧
good_list_nodes Ln ∧ is_restricted (hypermap_of_list Ln) ⇒ …` 的依赖形折算，
JcajyduShell 头注折算表），跨型段由 `rxNumTransportBridge` 真证消槽；
RXOKSKC / DAKEFCC / Iso.trans 在 `jcajyduShell` 内逐段对应（HOL :53-89
逐步对照见其头注）。结论槽与 Assembly `jcajydu`（:2509）逐字同形。 -/
theorem jcajyduOfNum (hp : restrictedHypermapsArePlaneGraphsV4)
    {α : Type*} [DecidableEq α] (H : Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Graph, PlaneGraphs g ∧ GoodGraphV4 g ∧
      ∃ H' : Hypermap (ℕ × ℕ), IsHypermapOfListTl g.fgraph H' ∧ H.Iso H' :=
  jcajyduShell hp rxNumTransportBridge H hres

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三
`[propext, Classical.choice, Quot.sound]`，零 sorryAx——本件吃显式前提
槽 hp、体为单行装配 rxNumTransportBridge 真证）。 -/
#print axioms Kepler.Text.TameSpine.jcajyduOfNum
