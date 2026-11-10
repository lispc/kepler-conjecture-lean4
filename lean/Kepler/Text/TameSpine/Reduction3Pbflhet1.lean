/-
  Kepler.Text.TameSpine.Reduction3Pbflhet1 — tame-corr nb3：PBFLHET 单步链
  nc3 三件 + NCVIBWU nc2 两小叶（塔层 i 形）+ 余量 indexf_two_point。

  ┌─ 归属对账（HOL → spine 塔层 i 形）─────────────────────────────
  │ §0 nc2 两小叶（工单 2；两条 V0 形查重命中 ⇒ 薄包装零重落）：
  │  · `indexfYtransEqLm1Spine`（HOL Ncvibwu.indexf_ytrans_eq_l_m1，
  │    NCVIBWU.hl:209，R-index 形）＝ `aq10_indexfYtransEqLm1`（Leaf10，
  │    HOL AQ7.hl:39 `_v0`，spine V0 已在库）在塔层 i 实例化。
  │    查重三方记账（工单要求）：chain `PwssratTail.indexfYtransEqLM1`
  │    （r-index、chain 载体）与 aq13 `qAnchorFIdx`（private、face-index、
  │    chain 载体）均非 spine 塔层公开形——本笔落的 spine 塔层形不撞。
  │  · `nextMarkCaseMemSpine`（HOL Ncvibwu.next_mark_case_mem，
  │    NCVIBWU.hl:333-424）＝ `aqs_nextMarkCaseMem`（Leaf12T，HOL
  │    AQ12.hl:3032 `_v0`）塔层 i 实例化。
  │    **nb2 勘误**：nb2 DELIVERY §5.2 曾记 next_mark_case_mem spine ✗
  │    ——系 grep 前缀漏配（`aqs_nextMarkCaseMem`），V0 形实已在库。
  │ §1 nc3 单步链三件（工单 1）：
  │  · `inRtransSucNotRtrans`（PBFLHET.hl:122）：V0 形查重命中
  │    `inRtransSucNotRtransNewV0`（JcajyduAqSnd，HOL HOJODCM.hl:107
  │    `in_rtrans_suc_not_rtrans_new_v0`——PBFLHET:122 的 i=0 孪生）⇒
  │    塔层 i 薄包装（aqiunpp3 供标记件 + 面表 congr 换元到 f）。
  │  · `indexfInRtransSucNotRtrans`（PBFLHET.hl:166）：件一 + PPLHULJ
  │    （pplhuljV0）+ y≠z（hqymrtx3List）+ indexf_betwn_eq/indexf_add_*
  │    纯算术（私件 indexfBetweenArith 收口，TameList3 全族）。
  │  · `eqIndexfInRtransSucNotRtrans`（PBFLHET.hl:210）：indexf_n
  │    （f 上）把 NCVIBWU（`ncvibwuTowerSpine`，nb2 落 32d1bf30）的
  │    轨道步折回 d，一步反写——HOL 证体的 DICH/ASM 尾墙在 Lean 侧
  │    坍缩为 `indexfN` + `symm`（NCVIBWU 通用 i 塔层形直接消费，
  │    零 betwn 位置账）。
  │ §2 余量：`indexfTwoPointInRtransSucNotRtrans`（PBFLHET.hl:281，
  │    消费 next_mark_case_mem）：nextMarkCaseMemSpine 两支——
  │    w = l'y 支 h1 自爆（indexf_refl = 0）；w ∈ betwn r₁ z y 支
  │    indexf_add_betwn（z,w,y）+ indexf_add_left（w,d,y 与 w,d1,y）
  │    + indexf_add_right（z,d,y 与 z,d1,y）方程算术 omega 收口
  │    （HOL 的 DICH 位置账在 Lean 方程化后零消费）。
  └────────────────────────────────────────────────────────────────

  ┌─ 勘误（AGENTS §7，写进交付）───────────────────────────────────
  │ ① 工单余量清单勘误：`lt_from_z_indexf_in_rtrans_suc_not_rtrans`
  │    （PBFLHET.hl:347）实测消费 `properties_of_ytrans0` 与
  │    `lt_indexf_in_rtrans_suc_not_rtrans`（均 QCDVKEA 依赖件），
  │    `INDUCT_MEM_MAIN_RESULT`（:374）仅消费 lt_from_z——两件为
  │    QCDVKEA **传递阻塞**，非"非 QCDVKEA 件"；本轮不落（dispatch
  │    §3 的余量清单第三件修正为仅 indexf_two_point）。
  │ ② J4 审计 §2b 勘误（betwn_ztran_ytrans_suc_const，KBWPBHQ.hl:623）：
  │    其证体实测跨 :623–:702，消费 27 名，其中 6 名为未落阻塞件：
  │    `Pnxvwfs.ytrans_in_suc`、`Pnxvwfs.ytran_suc_betwn_z_z_suc`、
  │    `Pbflhet.ztrans_suc_in_ztran_w`、`Pbflhet.w_betwn_ztrans_ytran0`、
  │    `Pbflhet.PBFLHET`、`Pnxvwfs.PNXVWFS2`（另有 `trans_indexf_suc`
  │    消费 OHCGKFU 通用 i 形 ✗、`Qcdvkea.QCDVKEA` 通用 i spine 形
  │    在 aq13 选型中）。审计 §2b 仅读 :623–665 致闭包截断——
  │    "单补 ztrans_in_suc 即可解冻 OBDATYB"不成立：该件深居
  │    nc4–nc7 + PNXVWFS2 下游，J4 的 OBDATYB 冻结维持。
  │ ③ properties_of_ytrans0（编排者建议的余量首位）：真塔归纳属实，
  │    且其证体消费 Qcdvkea.QCDVKEA 通用 i（spine 形待 aq13 载体选型）
  │    ——本轮不落，防与 aq13 在飞撞车。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull）；消费件（aqiunpp3 /
  │ aq10_indexfYtransEqLm1 / aqs_nextMarkCaseMem / inRtransSucNotRtransNewV0 /
  │ pplhuljV0 / ytransMemRtrans / memZtransRtransSpine / ncvibwuTowerSpine /
  │ rtransCat / TameList3 indexf-betwn 族）同世界零混合；泛 α 小件
  │ （indexfBetweenArith）无 BEq 接触面；零 Dart 载体件。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans
import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans2
import Kepler.Text.TameSpine.Reduction3NcvibwuTower
import Kepler.Text.TameSpine.Reduction3QcdvkeaTower
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.TameSpine.JcajyduAqLeaf10
import Kepler.Text.TameSpine.JcajyduAqLeaf12T
import Kepler.Text.TameSpine.JcajyduAqTowerBase
import Kepler.Text.TameSpine.JcajyduAqZIndexf
import Kepler.Text.TameSpine.JcajyduAqSnd

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl findFaceDarts_nodup
  findFaceDarts_congr_of_mem)

/-! ## §0 nc2 两小叶：NCVIBWU 塔层 i 形（V0 薄包装） -/

/-- **HOL `Ncvibwu.indexf_ytrans_eq_l_m1`**（NCVIBWU.hl:209，R-index 形）：
`¬final@i ∧ next_el (rtrans i) x = w ⇒
indexf w (l'y(i)) (rtrans i) = l'm (rtrans i) x`。
证 = `aq10_indexfYtransEqLm1`（HOL AQ7.hl:39 `_v0` 的 spine 形，Leaf10
在库）在塔层 (ntransSpine i, rtransSpine i) 实例化：标记件由 aqiunpp3
供给；`next_el (rtrans i) x = f_list x`（marked 合取 6）桥接 w 的两种
拼写。查重：V0 形已在库零重落；chain 侧 PwssratTail 形 / aq13
qAnchorFIdx（private）不同载体不同形，零冲突。 -/
theorem indexfYtransEqLm1Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {w : ℕ × ℕ} (hw : nextEl (rtransSpine L N r x i) x = w) :
    indexf w (ytransSpine L N r x i) (rtransSpine L N r x i)
      = lMSpine L (rtransSpine L N r x i) x := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have heq : nextEl (findFaceDarts L x) x = w := by
    rw [← hw, hmr.1.2.2.2.2.2.1]
    rfl
  have h := aq10_indexfYtransEqLm1 L hL hgn hmr hf
  rw [heq] at h
  exact h

/-- **HOL `Ncvibwu.next_mark_case_mem`**（NCVIBWU.hl:333-424）塔层 i 形：
`¬final@i ⇒ w = l'y(i) ∨ w ∈ betwn (rtrans i) (l'z(i)) (l'y(i))`。
证 = `aqs_nextMarkCaseMem`（HOL AQ12.hl:3032 `_v0` 的 spine 形，Leaf12T
在库）塔层 i 直投（aqiunpp3 供标记件；ytrans/ztrans 定义级换拼）。 -/
theorem nextMarkCaseMemSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    w = ytransSpine L N r x i ∨
      w ∈ between (rtransSpine L N r x i) (ztransSpine L N r x i)
        (ytransSpine L N r x i) :=
  aqs_nextMarkCaseMem L hL hgn (aqiunpp3 L hL i hta hgn hm) hf hfind hw

/-! ## §1 nc3：PBFLHET 单步链三件 -/

/-- **HOL `Pbflhet.in_rtrans_suc_not_rtrans`**（PBFLHET.hl:122）塔层 i 形：
`d ∈ rtrans(i+1) ∧ d ∉ rtrans(i) ⇒ d ∈ betwn f (l'y(i)) (l'z(i))`。
证 = V0 形查重命中 `inRtransSucNotRtransNewV0`（JcajyduAqSnd，HOL
HOJODCM.hl:107 `in_rtrans_suc_not_rtrans_new_v0`，即 PBFLHET:122 的
i=0 孪生）在塔层 (ntransSpine i, rtransSpine i) 实例化：标记件由
aqiunpp3 供给；l'y 处 face 表经 congr 换元到 f（PPLHULJ 供 l'y ∈
face x）。前提子集：HOL 的 f/w 数据件在证体零消费（经由 congr 间接
入场），塔层形按需保留 f/w 以对齐消费面。 -/
theorem inRtransSucNotRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hd0 : d ∉ rtransSpine L N r x i) :
    d ∈ between f (ytransSpine L N r x i) (ztransSpine L N r x i) := by
  have hfi : ¬ finalListSpine L (rtransSpine L N r x i) :=
    finalListInductSpine L N r x i hf
  have hmr := aqiunpp3 L hL i hta hgn hm
  obtain ⟨hyf, hzf, _⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x
      (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hcongY : findFaceDarts L (lYSpine L (rtransSpine L N r x i) x) = f :=
    (findFaceDarts_congr_of_mem hL.1 hxd hyf).trans hfind
  rw [rtransSuccSpine L N r x i] at hd1
  have hv0 := inRtransSucNotRtransNewV0 L hL hgn hunL hmr hfi hd1 hd0
  rw [hcongY] at hv0
  rw [show ytransSpine L N r x i = lYSpine L (rtransSpine L N r x i) x from rfl,
      show ztransSpine L N r x i
        = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl]
  exact hv0

/-- 窗口位置纯算术（HOL PBFLHET.hl:166-209 证体的 ARITH 尾墙）：
`y,z,w,d ∈ f ∧ y ≠ z ∧ d ∈ betwn f y z ∧ w→y < w→z ⇒
w→d < w→z ∧ w→y < w→d`。indexf_betwn_eq 出界、indexf_add_betwn/
add_left/add_right 三方程，omega 收口。 -/
private theorem indexfBetweenArith {f : List (ℕ × ℕ)} {w y z d : ℕ × ℕ}
    (hfnd : f.Nodup) (hwf : w ∈ f) (hyf : y ∈ f) (hzf : z ∈ f)
    (hne : y ≠ z) (hbet : d ∈ between f y z)
    (hlt : indexf w y f < indexf w z f) :
    indexf w d f < indexf w z f ∧ indexf w y f < indexf w d f := by
  obtain ⟨hp1, hp2⟩ := (indexfBetwnEq hne hfnd hyf hzf).mp hbet
  have hA := indexfAddLeft hwf hyf hzf (Nat.le_of_lt hlt)
  have hB := indexfAddBetwn hne hfnd hyf hbet hzf
  have hdf : d ∈ f := betwnMem hbet
  have hdzle : indexf d z f ≤ indexf w z f := by omega
  have hC := indexfAddRight hwf hdf hzf hdzle
  omega

/-- **HOL `Pbflhet.indexf_in_rtrans_suc_not_rtrans`**（PBFLHET.hl:166）
塔层 i 形：`w→d < w→l'z(i) ∧ w→l'y(i) < w→d`（face 上）。
证 = 件一（窗口成员）+ PPLHULJ（pplhuljV0：w→l'y < w→l'z）+ y ≠ z
（hqymrtx3List）+ 私件 indexfBetweenArith。 -/
theorem indexfInRtransSucNotRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hd0 : d ∉ rtransSpine L N r x i) :
    indexf w d f < indexf w (ztransSpine L N r x i) f
      ∧ indexf w (ytransSpine L N r x i) f < indexf w d f := by
  have hbet := inRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw hd1 hd0
  have hfi := finalListInductSpine L N r x i hf
  have hmr := aqiunpp3 L hL i hta hgn hm
  obtain ⟨hyf, hzf, hlt⟩ := pplhuljV0 L hL hgn hunL hmr hfi
  rw [hfind] at hlt hyf hzf
  rw [hw] at hlt
  have hne := hqymrtx3List L hL hgn hunL hmr hfi
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  rw [show ytransSpine L N r x i = lYSpine L (rtransSpine L N r x i) x from rfl,
      show ztransSpine L N r x i
        = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl] at hbet ⊢
  exact indexfBetweenArith hfnd hwf hyf hzf hne hbet hlt

/-- **HOL `Pbflhet.eq_indexf_in_rtrans_suc_not_rtrans`**（PBFLHET.hl:210）
塔层 i 形：`indexf w d f = indexf w d (rtrans(i+1))`。
证 = NCVIBWU 通用 i 塔层形（`ncvibwuTowerSpine`，nb2 落 32d1bf30）在
j := w→d 处给轨道步 ∈ r(i+1) 且其 r(i+1)-indexf 恰为 j；`indexf_n`
（f 上，d ∈ f 由件一窗口 ⊆ 面）把轨道步折回 d——HOL 尾墙的
DICH/ASM 位置账在 Lean 侧坍缩为一次 `rw [hdn]` + `symm`。 -/
theorem eqIndexfInRtransSucNotRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd1 : d ∈ rtransSpine L N r x (i + 1))
    (hd0 : d ∉ rtransSpine L N r x i) :
    indexf w d f = indexf w d (rtransSpine L N r x (i + 1)) := by
  have h1 := indexfInRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw hd1 hd0
  have hfi := finalListInductSpine L N r x i hf
  have hj : indexf w d f ≤ indexf w (ztransSpine L N r x i) f := Nat.le_of_lt h1.1
  obtain ⟨-, hidx⟩ := ncvibwuTowerSpine L hL hta hgn hm i hfi hfind hw hj
  have hbet := inRtransSucNotRtrans L hL hta hgn hunL hm i hf hfind hw hd1 hd0
  have hdf : d ∈ f := betwnMem hbet
  have hwf : w ∈ f := by
    rw [← hw, ← hfind]
    exact aq10_memNextMarkInface L hL hgn hm
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact findFaceDarts_nodup hL.1 x
  have hdn : (nextEl f)^[indexf w d f] w = d := indexfN hwf hdf hfnd
  rw [hdn] at hidx
  exact hidx.symm

/-! ## §2 余量：indexf_two_point（PBFLHET.hl:281） -/

/-- **HOL `Pbflhet.indexf_two_point_in_rtrans_suc_not_rtrans`
（PBFLHET.hl:281）塔层 i 形**：`d, d1 ∈ rtrans(i)`、
`w→d < w→l'y(i)`（rtrans(i) 上）、`w→d1 < w→d` ⇒
`l'z(i)→d1 < l'z(i)→d`（rtrans(i) 上）。
证 = `nextMarkCaseMemSpine` 两支：w = l'y 支 h1 与 indexf_refl 相抵
自爆；w ∈ betwn r₁ z y 支以 indexf_add_betwn（z,w,y）+ indexf_add_left
（w,d,y / w,d1,y）+ indexf_add_right（z,d,y / z,d1,y）五个方程
omega 收口——HOL 的 DICH 位置账在方程化后零消费（零位置分证）。 -/
theorem indexfTwoPointInRtransSucNotRtrans (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d d1 : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x i)
    (hd1 : d1 ∈ rtransSpine L N r x i)
    (h1 : indexf w d (rtransSpine L N r x i)
        < indexf w (ytransSpine L N r x i) (rtransSpine L N r x i))
    (h2 : indexf w d1 (rtransSpine L N r x i)
        < indexf w d (rtransSpine L N r x i)) :
    indexf (ztransSpine L N r x i) d1 (rtransSpine L N r x i)
      < indexf (ztransSpine L N r x i) d (rtransSpine L N r x i) := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hwr : w ∈ rtransSpine L N r x i := by
    have hw' : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
    rw [← hw']
    exact aq10_nextMarkMemRTrans L hL hgn hmr
  have hyl : lYSpine L (rtransSpine L N r x i) x ∈ rtransSpine L N r x i :=
    ytransMemRtrans L hL hgn hmr hf
  have hzl : lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
      ∈ rtransSpine L N r x i := memZtransRtransSpine L hL hgn hunL hta hm i hf
  have hrnd : (rtransSpine L N r x i).Nodup :=
    (normalListUniqNonnil hmr.1.2.1 hmr.1.2.2.1).1
  have hcase := nextMarkCaseMemSpine L hL hta hgn hm i hf hfind hw
  rw [show ytransSpine L N r x i = lYSpine L (rtransSpine L N r x i) x from rfl,
      show ztransSpine L N r x i
        = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl] at hcase
  rw [show ytransSpine L N r x i = lYSpine L (rtransSpine L N r x i) x from rfl] at h1
  rw [show ztransSpine L N r x i
    = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl]
  rcases hcase with heq | hbetW
  · rw [heq, indexfRefl hyl] at h1
    omega
  · have hne : lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
        ≠ lYSpine L (rtransSpine L N r x i) x :=
      Ne.symm (hqymrtx3List L hL hgn hunL hmr hf)
    have hE1 := indexfAddBetwn hne hrnd hzl hbetW hyl
    have hE2 := indexfAddLeft hwr hd hyl (Nat.le_of_lt h1)
    have hE2' := indexfAddLeft hwr hd1 hyl (by omega)
    have hE3 := indexfAddRight hzl hd hyl (by omega)
    have hE3' := indexfAddRight hzl hd1 hyl (by omega)
    omega

/-! ## §3 余量追加：两枚 V0 薄包装（冻结件下游消费路径铺轨） -/

/-- **HOL `Pbflhet.indexf_const_le_indexf_ytrans`**（PBFLHET.hl:409）
塔层 i 形：`MEM d (rtrans i) ∧ indexf w d (rtrans i) ≤ indexf w (l'y(i)) (rtrans i)
⇒ indexf w d (rtrans i) = indexf w d f`。
证 = `aq10_indexfConstLe`（HOL AQ7.hl:128 `_v0` 的 spine 形，Leaf10 在库）
塔层 i 实例化（aqiunpp3 供标记件；w 经 hfind/hw 桥接面锚拼写）。 -/
theorem indexfConstLeIndexfYtransSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {d : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x i)
    (hle : indexf w d (rtransSpine L N r x i)
      ≤ indexf w (ytransSpine L N r x i) (rtransSpine L N r x i)) :
    indexf w d (rtransSpine L N r x i) = indexf w d f := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hweq : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
  rw [show ytransSpine L N r x i = lYSpine L (rtransSpine L N r x i) x from rfl] at hle
  rw [← hweq] at hle
  rw [← hweq, ← hfind]
  exact aq10_indexfConstLe L hL hgn hmr hf hd hle

/-- **HOL `Kbwpbhq.next_el_power_trans_eq_f`**（KBWPBHQ.hl:391）塔层 i 形：
`n ≤ indexf w (l'y(i)) (rtrans i) ⇒
(next_el (rtrans i))^n w = (next_el f)^n w`。
证 = `aqs_nextElPowerTransEqF`（HOL AQ12.hl:2907 `_v0` 的 spine 形，
Leaf12T 在库）塔层 i 实例化。消费面：betwn_ztran_ytrans_suc_const
（KBWPBHQ:623，冻结件）与 CASES2 下游铺轨。 -/
theorem nextElPowerTransEqFSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {n : ℕ} (hn : n ≤ indexf w (ytransSpine L N r x i)
      (rtransSpine L N r x i)) :
    (nextEl (rtransSpine L N r x i))^[n] w
      = (nextEl (findFaceDarts L x))^[n] w := by
  have hmr := aqiunpp3 L hL i hta hgn hm
  have hweq : nextEl (findFaceDarts L x) x = w := by rw [hfind, hw]
  rw [show ytransSpine L N r x i = lYSpine L (rtransSpine L N r x i) x from rfl] at hn
  exact aqs_nextElPowerTransEqF L hL hgn hmr hf hweq hn

/-! ## §4 nc4 首件：properties_of_ytrans0（真塔归纳；QCDVKEA 已解锁） -/

/-- **HOL `Pbflhet.properties_of_ytrans0`**（PBFLHET.hl:74-121）塔层 i 形，
四合取：`indexf w (l'y(0)) f = indexf w (l'y(0)) (rtrans i)` ∧
`indexf w (l'y(0)) f < indexf w (l'z(i)) f` ∧
`indexf w (l'y(0)) f ≤ indexf w (l'y(i)) f` ∧
`MEM (l'y(0)) (rtrans i)`。
证（与 HOL 同构 i 归纳）：零支 = 双 indexf 锚（face 侧 indexfYtransEqLm
+ loop 侧 aq10_indexfYtransEqLm1 同为 l'm）+ PPLHULJ_v0 + ytransMemRtrans；
步支 = FINAL_LIST_INDUCT（前提下传给 IH）+ FINAL_LIST_INDUCT1（j:=0 供
¬final@0）+ PPLHULJ@0/@k+1 + QCDVKEA 塔层形（`qcdvkeaTowerSpine`，续 828
c872ae5b 落库）+ NCVIBWU 塔层形（`ncvibwuTowerSpine`）+ indexf_n（f 上）折回
y0。零支/步支全部在库件直投，零新几何。 -/
theorem propertiesOfYtrans0Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    indexf w (ytransSpine L N r x 0) f
        = indexf w (ytransSpine L N r x 0) (rtransSpine L N r x i)
      ∧ indexf w (ytransSpine L N r x 0) f
        < indexf w (ztransSpine L N r x i) f
      ∧ indexf w (ytransSpine L N r x 0) f
        ≤ indexf w (ytransSpine L N r x i) f
      ∧ ytransSpine L N r x 0 ∈ rtransSpine L N r x i := by
  revert hf
  induction i with
  | zero =>
    intro hf
    -- 零支拼写：ytrans/ztrans/rtrans 0 = l'y/l'z(初始态)/r
    rw [show ytransSpine L N r x 0 = lYSpine L r x from rfl,
        show ztransSpine L N r x 0 = lZSpine L N r x from rfl,
        show rtransSpine L N r x 0 = r from rfl]
    refine ⟨?_, ?_, le_refl _, ytransMemRtrans L hL hgn hm hf⟩
    · have h := indexfYtransEqLm L hL hgn hunL hm hf
      have h1 := aq10_indexfYtransEqLm1 L hL hgn hm hf
      rw [show nextEl (findFaceDarts L x) x = w from (by rw [hfind, hw])] at h h1
      rw [show findFaceDarts L x = f from hfind] at h
      exact h.trans h1.symm
    · obtain ⟨-, -, hlt⟩ := pplhuljV0 L hL hgn hunL hm hf
      rw [hfind, hw] at hlt
      exact hlt
  | succ k ih =>
    intro hf
    have hfi := finalListInductSpine L N r x k hf
    have hfk := ih hfi
    -- IH 拼写换元（ytrans/ztrans → lY/lZ(k)）
    rw [show ytransSpine L N r x 0 = lYSpine L r x from rfl,
        show ztransSpine L N r x k
          = lZSpine L (ntransSpine L N r x k) (rtransSpine L N r x k) x from rfl,
        show ytransSpine L N r x k
          = lYSpine L (rtransSpine L N r x k) x from rfl] at hfk
    -- ¬final@0（FINAL_LIST_INDUCT1 逆链）
    have hnf0 : ¬ finalListSpine L (rtransSpine L N r x 0) :=
      (finalListInduct1Spine L N r x k hfi) 0 (Nat.zero_le k)
    rw [show rtransSpine L N r x 0 = r from rfl] at hnf0
    -- PPLHULJ@0 与 @k+1
    obtain ⟨hyf0, -, hlt0⟩ := pplhuljV0 L hL hgn hunL hm hnf0
    rw [hfind] at hlt0 hyf0
    rw [hw] at hlt0
    have hmr1 := aqiunpp3 L hL (k + 1) hta hgn hm
    obtain ⟨hyf1, hzf1, hlt1⟩ := pplhuljV0 L hL hgn hunL hmr1 hf
    rw [hfind, hw] at hlt1
    -- 锚拼写统一（y0 = l'y(0) = lYSpine L r x）
    rw [show ytransSpine L N r x 0 = lYSpine L r x from rfl,
        show ztransSpine L N r x (k + 1)
          = lZSpine L (ntransSpine L N r x (k + 1)) (rtransSpine L N r x (k + 1)) x from rfl,
        show ytransSpine L N r x (k + 1)
          = lYSpine L (rtransSpine L N r x (k + 1)) x from rfl] at ⊢
    have hfnd : f.Nodup := by
      rw [← hfind]
      exact findFaceDarts_nodup hL.1 x
    have hwf : w ∈ f := by
      rw [← hw, ← hfind]
      exact aq10_memNextMarkInface L hL hgn hm
    -- (4)@k+1 与 (1)@k+1：NCVIBWU 塔层形 + indexf_n 折回 y0
    have hq := qcdvkeaTowerSpine L hL hta hgn hm k hf hfind hw
    rw [show ztransSpine L N r x k
        = lZSpine L (ntransSpine L N r x k) (rtransSpine L N r x k) x from rfl,
        show ytransSpine L N r x (k + 1)
          = lYSpine L (rtransSpine L N r x (k + 1)) x from rfl] at hq
    obtain ⟨hmem, hidx⟩ := ncvibwuTowerSpine L hL hta hgn hm k hfi hfind hw
      (Nat.le_of_lt hfk.2.1)
    have hdn : (nextEl f)^[indexf w (lYSpine L r x) f] w = lYSpine L r x :=
      indexfN hwf hyf0 hfnd
    rw [hdn] at hidx hmem
    refine ⟨hidx.symm, ?_, ?_, hmem⟩
    · -- (2)@k+1：w→y0 < w→l'z(k) ≤ w→l'y(k+1) < w→l'z(k+1)
      omega
    · -- (3)@k+1：w→y0 < w→l'z(k) ≤ w→l'y(k+1)
      omega

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.indexfYtransEqLm1Spine
#print axioms Kepler.Text.TameSpine.nextMarkCaseMemSpine
#print axioms Kepler.Text.TameSpine.inRtransSucNotRtrans
#print axioms Kepler.Text.TameSpine.indexfInRtransSucNotRtrans
#print axioms Kepler.Text.TameSpine.eqIndexfInRtransSucNotRtrans
#print axioms Kepler.Text.TameSpine.indexfTwoPointInRtransSucNotRtrans
#print axioms Kepler.Text.TameSpine.indexfConstLeIndexfYtransSpine
#print axioms Kepler.Text.TameSpine.nextElPowerTransEqFSpine
#print axioms Kepler.Text.TameSpine.propertiesOfYtrans0Spine
