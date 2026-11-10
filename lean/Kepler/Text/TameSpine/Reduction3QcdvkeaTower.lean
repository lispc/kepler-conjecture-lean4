/-
  Kepler.Text.TameSpine.Reduction3QcdvkeaTower — QCDVKEA 主件（QCDVKEA.hl:64）的
  spine 载体：单步形 `qcdvkeaV0Spine` + 通用 i 塔层形 `qcdvkeaTowerSpine`
  （N-A 主塔末件；与 tame-corr nb2 `ncvibwuTowerSpine` 同族）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ QCDVKEA.hl:64-157 `QCDVKEA`：
  │   transform_assumption_v2 L ∧ good_list L ∧ good_list_nodes L ∧
  │   ¬final_list L (rtrans L N r x (SUC i)) ∧ marked_list L N r x ∧
  │   find_face L x = f ∧ next_el f x = w ⇒
  │   indexf w (ztrans L N r x i) f ≤ indexf w (ytrans L N r x (SUC i)) f
  │ `qcdvkeaTowerSpine` = 该陈述的 spine 逐字形（TAV2 ↦
  │ `transformAssumptionSpine`，零额外槽）；证 = 单步形 `qcdvkeaV0Spine` 在塔层
  │ (ntransSpine i, rtransSpine i) 直投 + `aqiunpp3` + `rtransSuccSpine` 折叠
  │ （nb2 探针 probe_qcdvkeaTower-nb2 的 hV0 槽由本文件单步形填实）。
  │ `qcdvkeaV0Spine`（单步形，证体三段与 HOL 同构）：
  │ ① y-index 锚 = 树内 `indexfYtransEqLm`（JcajyduAqZIndexf:136，
  │    Pplhulj.hl:114 的 spine face-index 形，状态 1 实例）；
  │ ② min_num_le + 非空支（HOL :124-150 逆否）= sInf 极小性 +
  │    `wDepartNonempty`（{P}=∅ ⇒ final_list）；
  │ ③ 三角割支（HOL :94-120）= `ncvibwuV0FullSpine` 于 i、i+1 两次 + indexf_n
  │    ⇒ 状态 1 的 l'm 谓词在 i 处不成立。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体选型定谳（R1 世界记账）───────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull，lMSpine = sInf），与 nb2
  │ 塔族零混合。未走「chain `qcdvkeaV0` + ChainSpineBridge」：chain 件携
  │ AqiunppSlot（chain TAV2）与 hs 槽，翻译回 spine 会把 chain 槽带进 spine 塔，
  │ 与塔族的 `transformAssumptionSpine` 单槽不同构；且 spine 侧 face-index 锚
  │ 已在库（chain 侧无，故 chain V0 自带锚/界两件），直证反而更短。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓双零写入；既有文件零触碰。
-/

import Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans
import Kepler.Text.TameSpine.Reduction3NcvibwuIndexMain

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face nextEl_mem_of_mem)

/-! ## §1 非空支（QCDVKEA.hl:124-150 逆否） -/

/-- 非空支：`¬final_list L r ⇒ {m | P m} ≠ ∅`（P m := l'm 谓词）。
{P}=∅ 时 `indexf_n` 把 r 的任一元写成 x 的 nextEl 幂，逐点得
`f_list L d = next_el r d`，即 final（Reduction3QcdvkeaV0 私件的 spine 形重推导）。 -/
private theorem wDepartNonempty {L : fgraph ℕ} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hx1 : x ∈ r) (hrnd : r.Nodup) (hnext : nextEl r x = fList L x)
    (hf : ¬ finalListSpine L r) :
    ({m : ℕ | (nextEl r)^[m + 2] x ≠ fList L ((nextEl r)^[m + 1] x)} : Set ℕ).Nonempty := by
  by_contra hempty
  apply hf
  intro d hd
  have hfx : fList L x ∈ r := by
    rw [← hnext]; exact nextEl_mem_of_mem hx1
  have hidx := indexfN hfx hd hrnd
  have hall : (nextEl r)^[indexf (fList L x) d r + 2] x
      = fList L ((nextEl r)^[indexf (fList L x) d r + 1] x) := by
    by_contra hbad
    exact hempty ⟨indexf (fList L x) d r, hbad⟩
  have hA : (nextEl r)^[indexf (fList L x) d r + 1] x = d := by
    rw [Function.iterate_succ_apply (nextEl r) (indexf (fList L x) d r) x, hnext]
    exact hidx
  have hB : (nextEl r)^[indexf (fList L x) d r + 2] x = nextEl r d := by
    have s : (nextEl r)^[indexf (fList L x) d r + 2] x
        = nextEl r ((nextEl r)^[indexf (fList L x) d r + 1] x) :=
      Function.iterate_succ_apply' (nextEl r) (indexf (fList L x) d r + 1) x
    rw [s, hA]
  rw [hA, hB] at hall
  exact hall.symm

/-! ## §2 QCDVKEA 单步形（spine 载体） -/

/-- **HOL `QCDVKEA`**（QCDVKEA.hl:64-157）的 spine 单步形（状态对一步）：
`marked_list L N r x ∧ ¬final_list L (rtrans L N r x 1) ⇒
indexf w (l'z L N r x) f ≤ indexf w (l'y L (rtrans L N r x 1) x) f`。
状态 1 的标记件由 `transformAssumptionSpine` 一步供给；锚 = `indexfYtransEqLm`
于状态 1；三角割支 = `ncvibwuV0FullSpine` 双实例。 -/
theorem qcdvkeaV0Spine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    (hf1 : ¬ finalListSpine L (rtransSpine L N r x 1))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf w (lZSpine L N r x) f
      ≤ indexf w (lYSpine L (rtransSpine L N r x 1) x) f := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  -- 状态 1 载体（TAV2 一步）
  have hm1 : MarkedListSpineFull hL (ntransSpine L N r x 1) (rtransSpine L N r x 1) x :=
    hta N r x hgn hm
  have hrnd1 : (rtransSpine L N r x 1).Nodup :=
    (normalListUniqNonnil hm1.1.2.1 hm1.1.2.2.1).1
  have hx1 : x ∈ rtransSpine L N r x 1 := hm1.1.2.2.2.1
  have hnext1 : nextEl (rtransSpine L N r x 1) x = fList L x := hm1.1.2.2.2.2.2.1
  have hf0 : ¬ finalListSpine L r := finalListInductSpine L N r x 0 hf1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩)
  have hxb : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hfpow : ∀ k : ℕ, (fList L)^[k] x = (nextEl f)^[k] x := by
    intro k
    rw [fListPowEqNextElPow L hL x hxb, hfind]
  have hw1 : nextEl (rtransSpine L N r x 1) x = w := by
    rw [hnext1]
    show nextEl (findFaceDarts L x) x = w
    rw [hfind]; exact hw
  have hwmem1 : w ∈ rtransSpine L N r x 1 := by
    rw [← hw1]; exact nextEl_mem_of_mem hx1
  -- ① y-index 锚（状态 1）
  have hanchor : indexf w (lYSpine L (rtransSpine L N r x 1) x) f
      = lMSpine L (rtransSpine L N r x 1) x := by
    have h := indexfYtransEqLm L hL hgn hunL hm1 hf1
    rwa [hfind, hw] at h
  rw [hanchor]
  -- ③ 三角割支：i < indexf w z f ⇒ NCVIBWU 于 i、i+1 ⇒ 谓词在 i 处不成立
  have h2 : ∀ i : ℕ, i < indexf w (lZSpine L N r x) f →
      ¬ ((nextEl (rtransSpine L N r x 1))^[i + 2] x
        ≠ fList L ((nextEl (rtransSpine L N r x 1))^[i + 1] x)) := by
    intro i hiZ
    obtain ⟨hmemI, hidxI⟩ := ncvibwuV0FullSpine L hL hgn hm hf0 hfind hw
      (j := i) (by omega)
    obtain ⟨hmemS, hidxS⟩ := ncvibwuV0FullSpine L hL hgn hm hf0 hfind hw
      (j := i + 1) (by omega)
    have hI0 : (nextEl (rtransSpine L N r x 1))^[i] w = (nextEl f)^[i] w := by
      have h1 := indexfN hwmem1 hmemI hrnd1
      rw [hidxI] at h1
      exact h1
    have hI1 : (nextEl (rtransSpine L N r x 1))^[i + 1] w = (nextEl f)^[i + 1] w := by
      have h1 := indexfN hwmem1 hmemS hrnd1
      rw [hidxS] at h1
      exact h1
    have hmid : (nextEl (rtransSpine L N r x 1))^[i + 1] x = (nextEl f)^[i] w := by
      rw [Function.iterate_succ_apply (nextEl (rtransSpine L N r x 1)) i x, hw1, hI0]
    have s1 : (nextEl (rtransSpine L N r x 1))^[i + 2] x
        = (nextEl (rtransSpine L N r x 1))^[i + 1] w := by
      have s : (nextEl (rtransSpine L N r x 1))^[i + 2] x
          = (nextEl (rtransSpine L N r x 1))^[i + 1] (nextEl (rtransSpine L N r x 1) x) :=
        Function.iterate_succ_apply (nextEl (rtransSpine L N r x 1)) (i + 1) x
      rw [s, hw1]
    have hfl : (nextEl f)^[i] w = (fList L)^[i + 1] x := by
      rw [← hw, ← Function.iterate_succ_apply (nextEl f) i x, ← hfpow]
    have e : (nextEl (rtransSpine L N r x 1))^[i + 2] x
        = fList L ((nextEl (rtransSpine L N r x 1))^[i + 1] x) := by
      rw [s1, hI1, hmid, hfl, ← Function.iterate_succ_apply' (fList L) (i + 1) x,
        hfpow, ← hw]
      exact (Function.iterate_succ_apply (nextEl f) (i + 1) x).symm
    intro hbad
    exact hbad e
  -- ② sInf 极小性 + 非空支
  have hne := wDepartNonempty hx1 hrnd1 hnext1 hf1
  by_contra hcon
  have hlt : lMSpine L (rtransSpine L N r x 1) x < indexf w (lZSpine L N r x) f := by
    omega
  have hmem : lMSpine L (rtransSpine L N r x 1) x
      ∈ ({m : ℕ | (nextEl (rtransSpine L N r x 1))^[m + 2] x
          ≠ fList L ((nextEl (rtransSpine L N r x 1))^[m + 1] x)} : Set ℕ) :=
    Nat.sInf_mem hne
  exact h2 _ hlt hmem

/-! ## §3 QCDVKEA 主件通用 i 塔层形（HOL QCDVKEA.hl:64） -/

/-- **HOL `QCDVKEA_concl`**（QCDVKEA.hl:64）的 spine 塔层 i 形（逐字）：
`¬final_list L (rtrans(i+1)) ⇒ indexf w (l'z(i)) f ≤ indexf w (l'y(i+1)) f`。
证 = `qcdvkeaV0Spine` 在塔层 (ntransSpine i, rtransSpine i) 直投 + `aqiunpp3` +
`rtransSuccSpine` 折叠（ztransSpine/ytransSpine 的 l'z/l'y 项 delta 同项）。 -/
theorem qcdvkeaTowerSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1)))
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w) :
    indexf w (ztransSpine L N r x i) f
      ≤ indexf w (ytransSpine L N r x (i + 1)) f := by
  have h := qcdvkeaV0Spine L hL hta hgn (aqiunpp3 L hL i hta hgn hm)
    (by rw [← rtransSuccSpine L N r x i]; exact hf) hfind hw
  rw [show ytransSpine L N r x (i + 1)
      = lYSpine L (rtransSpine L N r x (i + 1)) x from rfl,
    rtransSuccSpine L N r x i]
  exact h

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.TameSpine.qcdvkeaV0Spine
#print axioms Kepler.Text.TameSpine.qcdvkeaTowerSpine
#print axioms Kepler.Text.TameSpine.wDepartNonempty
