/-
  Kepler.Text.TameSpine.Reduction3NcvibwuSpineB1 — W2-件2 Wave B1：
  NCVIBWU-spine（i=0 剪枝共享件）的前半交付。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ PPLHULJ.hl:248 `PPLHULJ`（三合取）→ §1 pplhuljSpine（总装，3 行）
  │ Ncvibwu.hl:425 `NCVIBWU2` / :1132 `NCVIBWU3`（i=0 剪枝）→ §2 前半：
  │   **F-弧半件**（indexf w y < j ≤ indexf w z 的 ∈ r' 成员性）。
  │   后半（w..y 头段的 ∈ r' 与两半的 indexf 等式）+ 接缝报告见
  │   DELIVERY_2B §2/§3；本文件不含后者的任何未证洞（全部真证，零禁词）。
  └────────────────────────────────────────────────────────────────

  ┌─ 与 HOL 的关系（i=0 剪枝的理由）──────────────────────────────────
  │ NCVIBWU 主件结论在 i 上全称；但每步的结构完全相同（transform 一步
  │ 的形状不依赖 i），故 i=0 的陈述经**状态实例化**即覆盖任意 i：
  │ 消费者持 marked/¬final 于状态 (ntrans i, rtrans i)（aqiunpp3_top 供
  │ marked，¬final 为 NCVIBWU 前提），把 i=0 件的 (N, r) 换成
  │ (ntransSpine i, rtransSpine i) 直得。QCDVKEA 可用性判定见 DELIVERY_2B §4。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS ─────────────────────────────────────────────────────
  │ ① spine 岛载体（ntransSpine/rtransSpine/lYSpine/lZSpine），与件1/1a/
  │    Wave A 同制式；hgn 显式。
  │ ② `transform_assumption_v2` 不出槽（路线同件1：marked 传播由
  │    aqiunpp3_top 内部无条件形吸收；本文件未消费，照原文前提位缺席）。
  │ ③ §1 前提比 HOL 弱一档：HOL PPLHULJ 携带 ~final_list，本件两件只
  │    需 marked（pplhulj3V0 的已落形即如此，消费侧恒可实例化）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入（/tmp 岛编）；
  │ 既有文件零触碰。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3HbridgeElim
import Kepler.Text.TameSpine.TameList17

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl nextEl_mem_of_mem dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace)

variable {α : Type*}

/-! ## §0 幂成员私件（TameList3 私件同款重推导） -/

/-- nextEl 幂保成员。 -/
private theorem orbitMemB1 [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    {x : α} (hx : x ∈ s) : ∀ k : ℕ, (nextEl s)^[k] x ∈ s := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-! ## §1 PPLHULJ（spine 总装） -/

/-- **HOL `PPLHULJ`**（PPLHULJ.hl:248）：`l'y ∈ f ∧ l'z ∈ f ∧
indexf w l'y f < indexf w l'z f`（f = findFaceDarts L x、w = nextEl f x）。
组装 = markedLemmaYzInFace.1/.2 + pplhulj3V0（JcajyduAqZIndexf）。 -/
theorem pplhuljSpine (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    lYSpine L r x ∈ findFaceDarts L x ∧ lZSpine L N r x ∈ findFaceDarts L x ∧
      indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) (findFaceDarts L x)
        < indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) (findFaceDarts L x) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  obtain ⟨hy, hz⟩ := markedLemmaYzInFace L hL hgn hunL hm hf
  exact ⟨hy, hz, pplhulj3V0 L hL hgn hunL hm hf⟩

/-! ## §2 NCVIBWU-spine i=0 的 F-弧半件 -/

/-- **NCVIBWU-spine（i=0）F-弧成员性半件**：face 轨道自 w 的第 j 步落在
y..z 弧（indexf w y < j ≤ indexf w z）时 ∈ r' = rtransSpine 1
（F 段经 rtransCat 直投；j = indexf w z 边界即 d = l'z ∈ S 头）。 -/
theorem ncvibwuSpineV0FPart (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) {j : ℕ}
    (hj1 : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) (findFaceDarts L x) < j)
    (hj2 : j ≤ indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x)
      (findFaceDarts L x)) :
    (nextEl (findFaceDarts L x))^[j] (nextEl (findFaceDarts L x) x)
      ∈ rtransSpine L N r x 1 := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  obtain ⟨hyf, hzf⟩ := markedLemmaYzInFace L hL hgn hunL hm hf
  have hne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x := nextEl_mem_of_mem hxx
  have hfnd : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hjd : (nextEl (findFaceDarts L x))^[j] (nextEl (findFaceDarts L x) x)
      ∈ findFaceDarts L x := orbitMemB1 hwf j
  have hlt : j < (findFaceDarts L x).length := by
    have h1 := indexfLtSizel hwf hzf
    omega
  have hidx : indexf (nextEl (findFaceDarts L x) x)
      ((nextEl (findFaceDarts L x))^[j] (nextEl (findFaceDarts L x) x))
      (findFaceDarts L x) = j :=
    nextElnIndexf hwf hjd hfnd rfl hlt
  have hwyz : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x)
      (findFaceDarts L x) < indexf (nextEl (findFaceDarts L x) x)
        (lZSpine L N r x) (findFaceDarts L x) :=
    pplhulj3V0 L hL hgn hunL hm hf
  rcases Nat.lt_or_ge j (indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x)
    (findFaceDarts L x)) with hcase | hcase
  · -- j < indexf w z：d ∈ between f y z（indexfBetwnEq 双射）
    have hadd : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x) (findFaceDarts L x)
        + indexf (lYSpine L r x) ((nextEl (findFaceDarts L x))^[j] (nextEl (findFaceDarts L x) x))
          (findFaceDarts L x)
        = indexf (nextEl (findFaceDarts L x) x)
          ((nextEl (findFaceDarts L x))^[j] (nextEl (findFaceDarts L x) x))
          (findFaceDarts L x) :=
      indexfAddLeft hwf hyf hjd (le_of_lt (by rw [hidx]; exact hj1))
    have haddz : indexf (nextEl (findFaceDarts L x) x) (lYSpine L r x)
        (findFaceDarts L x)
        + indexf (lYSpine L r x) (lZSpine L N r x) (findFaceDarts L x)
        = indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x) (findFaceDarts L x) :=
      indexfAddLeft hwf hyf hzf (le_of_lt hwyz)
    have hb : (nextEl (findFaceDarts L x))^[j] (nextEl (findFaceDarts L x) x)
        ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) := by
      refine (indexfBetwnEq hne hfnd hyf hzf).mpr ⟨?_, ?_⟩
      · omega
      · omega
    have hcongr : findFaceDarts L (lYSpine L r x) = findFaceDarts L x :=
      findFaceDarts_congr_of_mem hL.1 hxd hyf
    have hb' : (nextEl (findFaceDarts L x))^[j] (nextEl (findFaceDarts L x) x)
        ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) := by
      rw [hcongr]
      exact hb
    rw [rtransCat L N r x hf hrnd]
    exact List.mem_append_right _ hb'
  · -- j = indexf w z：d = l'z，落在 S 头
    have hjeq : j = indexf (nextEl (findFaceDarts L x) x) (lZSpine L N r x)
        (findFaceDarts L x) := le_antisymm hj2 hcase
    subst hjeq
    have hzj : (nextEl (findFaceDarts L x))^[indexf (nextEl (findFaceDarts L x) x)
        (lZSpine L N r x) (findFaceDarts L x)] (nextEl (findFaceDarts L x) x)
        = lZSpine L N r x :=
      indexfN hwf hzf hfnd
    rw [hzj, rtransCat L N r x hf hrnd]
    exact List.mem_append_left _
      (List.mem_append_left _ (List.mem_cons_self ..))

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.pplhuljSpine
#print axioms Kepler.Text.TameSpine.ncvibwuSpineV0FPart
