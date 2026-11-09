/-
  Kepler.Text.Reduction4Subseg9 — W2-b P3-a：吃 AQIUNPP 件中唯一可即时交付件
  `final_assumption_mem_x_core`（reduction4.hl:519），AQIUNPP 照 Reduction5K5
  槽形惯例吃 Prop 槽（陈述用链侧 def 组装，装配面由 JcajyduRed2Tav2.aqiunpp
  供给）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/reduction4.hl`）──
  │ :519 `final_assumption_mem_x_core` → finalAssumptionMemXCore
  │   （reduction_K1 :2527 假设块 MEM 段第 1 槽消费）
  └────────────────────────────────────────────────────────────────

  ┌─ 逐件抽查结论（P2/P3 派单件；机器证据见 DELIVERY）──────────────
  │ P3 三件：mem_x_core:519 ✅ 本件（只吃 mem_fst_core ✓ + AQIUNPP 槽）；
  │ zpre_core_k:544 ❌ 额外闸 = Pbflhet.ztrans_in_suc（未落）+
  │   mem_uniq:171（又闸 PNXVWFS1/2）；yz_in_core:727 ❌ 额外闸 =
  │   properties_of_ytrans0 / lnrx_induction /
  │   core_split_normal_list_assumption_lemma / r_trans_eq_assumption_lemma
  │   （全未落）+ PNXVWFS1/2。
  │ P2 四件全部闸死在 Pnxvwfs 章（PNXVWFS1/2 未落，证体各 60+ 行、消费
  │   Pbflhet.FINAL_LIST_INDUCT1 / Qcdvkea.FINAL_LIST_INDUCT /
  │   ytrans_in_suc / ytran_suc_betwn_z_z_suc / ztrans_suc_in_ztran_w /
  │   w_betwn_ztrans_ytran0 / PBFLHET / indexf 机器——MoreLemma2a23:30
  │   头注明记该批「未含」）+ DIOWAAS（y_ne_z 前置，未落）+ Hojodcm.
  │   f_eq_next_el_x_v0（TameSpine TowerBase，链侧 import 不可）+
  │   Pwssrat.next_el_rotate_to_eq（未落）。TAV2 槽已解锁但非充分条件。
  │   explicit:1763 唯一缺 PNXVWFS1/2（其余全就位：prebatch_suc_explicit
  │   ✓ Reduction3Thm13 / prebatch1 ✓ t12_prebatch1 / scroll_flatten_map ✓
  │   Subseg8 / marked_list_uniq_core ✓ Subseg8 / mem_fst_core ✓ /
  │   transform_count_non0 ✓ Reduction3Thm11 / TAV2 槽 ✓）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与槽形 ──────────────────────────────────────────────────
  │ `mem_fst_core` ↦ Subseg4.finalAssumptionMemFstCore（F 组）；
  │ AQIUNPP 槽 `haq` = JcajyduRed2Tav2.aqiunpp 的陈述形（链侧 def 组装：
  │   markedList/ntrans/rtrans ↦ Reduction5Base+ChainListsL2，
  │   GoodListNodesTl ↦ TameLp:5278），装配面 = JcajyduRed2Tav2.aqiunpp
  │   L hL（签名逐槽同形，J5 折算零成本）；
  │ `newvertex_prepped` ↦ Reduction3DefsNewVertex.newvertexPrepped（陈述槽
  │   Prop 形；本件证体零消费，照 HOL 原文保留前提位）。
  │ 环安全：唯一 import = Reduction4Subseg4（F 组，Subseg8 同款闭包纪律）。
  │ 零 axiom/sorry/admit/native_decide；零 tracked 改动。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction4Subseg4
import Kepler.Text.Reduction3DefsNewVertex

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)
open Kepler.Text.Reduction5 (Dart parts core ntrans rtrans transformCount
  finalList)
open Kepler.Text.ChainLists (markedList)

/-- **AQIUNPP 槽**（HOL `AQIUNPP`，reduction3.hl:4047-4053 的陈述形；
链侧 def 组装，证明面 = JcajyduRed2Tav2.aqiunpp 签名逐槽同形）：
`markedList` 经任意 `i` 步变换保持。 -/
def AqiunppSlot (L : fgraph ℕ) (hL : GoodList L) : Prop :=
  ∀ (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL) (N : List (List Dart))
    (r : List Dart) (x : Dart),
    markedList L hL N r x → ∀ i : ℕ,
    markedList L hL (ntrans L N r x i) (rtrans L N r x i) x

/-- **HOL `final_assumption_mem_x_core`**（reduction4.hl:519-:532）：
`x` 经 `k` 步变换后仍在 core 中。证明（HOL :524-:532 逐步对照）：
`INTRO_TAC final_assumption_mem_fst_core [ntrans k; rtrans k; x]`
（mem_fst_core 在变换后的 N' r' 处实例化，SUBANTS = AQIUNPP 供变换后的
markedList），结论在 `u := x` 处使用，`MEM x r'` 槽取自变换后 marked_list
第 4 槽（HOL `ASM_MESON_TAC[marked_list]`）。

前提七项照 HOL 原文逐字保留（good_list ↦ hL 载体前提 DIFFERS-①；
newvertex_prepped/¬final_list/transform_count=k 三项本件证体零消费，
忠实保留前提位）。 -/
theorem finalAssumptionMemXCore (L : fgraph ℕ) (hL : GoodList L)
    (haq : AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (hnv : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : markedList L hL N r x)
    (hfin : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    x.1 ∈ core L (rtrans L N r x k) := by
  have hmk := haq hgn N r x hm k
  have hx : x ∈ rtrans L N r x k := hmk.2.2.2.1
  exact finalAssumptionMemFstCore L hL hmk x hx

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（编译即执行；预期 = 标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.Reduction4Idx.AqiunppSlot
#print axioms Kepler.Text.Reduction4Idx.finalAssumptionMemXCore
