/-
  Kepler.Text.TameSpine.Reduction3Pwssrat — PWSSRAT 主件（PWSSRAT.hl:584-759）
  的 spine 载体移植：`pwssratSpine`（通用 i，逐字陈述形）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ PWSSRAT.hl:584 `PWSSRAT_concl`：
  │   transform_assumption_v2 L ∧ good_list L ∧ good_list_nodes L ∧
  │   marked_list L N r x ∧ MEM d (rtrans L N r x i) ∧
  │   ¬final_list L (rtrans L N r x i) ⇒
  │   (MEM d (rtrans L N r x (SUC i)) ⇔
  │      indexf (ztrans L N r x i) d (rtrans L N r x i) ≤
  │      indexf (ztrans L N r x i) (ytrans L N r x i) (rtrans L N r x i))
  │ （**终态前提在状态 i**——QCDVKEA 教训逐字核对：非 (SUC i)）。
  │ 证体四案（HOL 同构）：
  │ ⓪ 结构：`rtrans (i+1) = ([l'z] ++ betwn (rtrans i) l'z l'y ++ [l'y])
  │    ++ betwn (find_face L l'y) l'y l'z`——`rtransSuccSpine`（一步折叠）
  │    + `rtransCat`（JcajyduRed2Trans，split_normal_list 显式形；HOL 的
  │    ASM_REWRITE[rtrans; transform_list; split_normal_list] 段）；
  │ ① ⇒：四案分流——d=l'z（indexfRefl，0 ≤）、d ∈ betwn r1 l'z l'y
  │    （`indexfBetwnEq` 0 < idx < idx l'y ⇒ ≤）、d=l'y（自 ≤）、
  │    d ∈ betwn (find_face L l'y) l'y l'z（face 弧点 = f^{k} l'y，
  │    1 ≤ k ≤ l'p ⇒ `fListPowYtransNotMem` ∉ r1，与 MEM d (rtrans i) 矛盾）；
  │    其中 k = indexf l'y d f 的上界 k < indexf l'y l'z f = l'p + 1 由
  │    `indexfBetwnEq` + `indexfYtransSucLp`（JcajyduAqZIndexf:207，
  │    AQ1.hl:284 的 spine 形）供，d = f^k l'y 由 `indexfN` + `fListPowEqNextElPow`；
  │ ② ⇐：`indexf_n` 两次（d = (next_el r1)^{idx d} l'z、l'y = (next_el r1)^{idx l'y} l'z）
  │    + `indexfBetwnEq` 分案（idx d = 0 ⇒ d = l'z；0 < idx d < idx l'y ⇒
  │    d ∈ betwn；idx d = idx l'y ⇒ d = l'y）——全部落在结构四案的前三支。
  │ 依赖全在库（状态 0 spine 形 + `aqiunpp3` 塔层一步）：memZtransRtransSpine
  │  （KbwpbhqNtrans:237，z ∈ r1 塔形）/ ytransMemRtrans（TowerBase:195）
  │  / hqymrtx3List（TameList17:383，z ≠ y）/ zMemFindFaceDarts
  │  （ZUnlock:71，z ∈ find_face y）/ memYtransListOfDarts（TowerBase:209）
  │  / indexfYtransSucLp / fListPowYtransNotMem（ZIndexf:207/:188）
  │  / fListPowEqNextElPow / indexfBetwnEq / indexfN / indexfRefl
  │  / findFaceDarts_nodup / dart_in_face / inbetween_inset / rtransCat
  │  / rtransSuccSpine / isRestrictedAllUniq / normalListUniqNonnil。
  │  状态 i 的标记件由 `aqiunpp3`（TAV2 一步，TameList17:255）供给。
  │  本证体不消费 nc3/nc4/nc5 的任何件。
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

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face nextEl_mem_of_mem
  findFaceDarts_nodup)

/-- **HOL `PWSSRAT_concl`**（PWSSRAT.hl:584）的 spine 塔层 i 形（逐字）：
`marked_list L N r x ∧ MEM d (rtrans i) ∧ ¬final_list L (rtrans i) ⇒
(MEM d (rtrans (i+1)) ⇔ indexf (l'z(i)) d (rtrans i) ≤
indexf (l'z(i)) (l'y(i)) (rtrans i))`。
状态 i 的标记件由 `aqiunpp3`（TAV2 一步）供给；结构 = `rtransSuccSpine`
+ `rtransCat`；双向 = `indexfBetwnEq`/`indexfN`/`indexfRefl` 位置账。 -/
theorem pwssratSpine (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    {d : ℕ × ℕ} (hd : d ∈ rtransSpine L N r x i)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    (d ∈ rtransSpine L N r x (i + 1) ↔
      indexf (ztransSpine L N r x i) d (rtransSpine L N r x i)
        ≤ indexf (ztransSpine L N r x i) (ytransSpine L N r x i)
            (rtransSpine L N r x i)) := by
  show (d ∈ rtransSpine L N r x (i + 1) ↔
    indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x) d
      (rtransSpine L N r x i)
    ≤ indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
        (lYSpine L (rtransSpine L N r x i) x) (rtransSpine L N r x i))
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hmI := aqiunpp3 L hL i hta hgn hm
  have hrnd1 : (rtransSpine L N r x i).Nodup :=
    (normalListUniqNonnil hmI.1.2.1 hmI.1.2.2.1).1
  have hz1 : lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
      ∈ rtransSpine L N r x i :=
    memZtransRtransSpine L hL hgn hunL hta hm i hf
  have hy1 : lYSpine L (rtransSpine L N r x i) x ∈ rtransSpine L N r x i :=
    ytransMemRtrans L hL hgn hmI hf
  have hzne : lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
      ≠ lYSpine L (rtransSpine L N r x i) x :=
    fun h => hqymrtx3List L hL hgn hunL hmI hf h.symm
  -- 结构：rtrans (i+1) = (([z] ++ betwn r1 z y) ++ [y]) ++ betwn (find_face L y) y z
  have hsplit : rtransSpine L N r x (i + 1)
      = ([lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x]
          ++ between (rtransSpine L N r x i)
              (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
              (lYSpine L (rtransSpine L N r x i) x)
          ++ [lYSpine L (rtransSpine L N r x i) x])
        ++ between (findFaceDarts L (lYSpine L (rtransSpine L N r x i) x))
            (lYSpine L (rtransSpine L N r x i) x)
            (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x) := by
    rw [rtransSuccSpine L N r x i]
    exact rtransCat L (ntransSpine L N r x i) (rtransSpine L N r x i) x hf hrnd1
  have hbt := indexfBetwnEq (y := d) hzne hrnd1 hz1 hy1
  constructor
  · -- ⇒：d ∈ rtrans(i+1) 四案
    intro hmem
    rw [hsplit] at hmem
    rcases List.mem_append.mp hmem with h123 | hC
    · rcases List.mem_append.mp h123 with h12 | hY
      · rcases List.mem_append.mp h12 with hZ | hA
        · -- d = l'z：indexf l'z l'z = 0 ≤
          have hdz := List.mem_singleton.mp hZ
          have h0 := indexfRefl hz1
          rw [hdz]
          omega
        · -- d ∈ betwn r1 l'z l'y：0 < idx d < idx l'y ⇒ ≤
          have h := hbt.mp hA
          omega
      · -- d = l'y：自 ≤
        have hdy := List.mem_singleton.mp hY
        exact le_of_eq (by rw [hdy])
    · -- d ∈ betwn (find_face L l'y) l'y l'z：face 弧点 ∉ r1，反证
      exfalso
      have hyd : lYSpine L (rtransSpine L N r x i) x ∈ listOfDarts L :=
        memYtransListOfDarts L hL hgn hmI hf
      have hyf : lYSpine L (rtransSpine L N r x i) x
          ∈ findFaceDarts L (lYSpine L (rtransSpine L N r x i) x) :=
        (dart_in_face L _).mpr hyd
      have hzf : lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
          ∈ findFaceDarts L (lYSpine L (rtransSpine L N r x i) x) :=
        zMemFindFaceDarts L hL hgn hunL hmI hf
      have hfnd : (findFaceDarts L (lYSpine L (rtransSpine L N r x i) x)).Nodup :=
        findFaceDarts_nodup hL.1 _
      have hdf : d ∈ findFaceDarts L (lYSpine L (rtransSpine L N r x i) x) :=
        Kepler.Graphs.inbetween_inset hC
      have hidx := (indexfBetwnEq (y := d) (Ne.symm hzne) hfnd hyf hzf).mp hC
      have hsuc := indexfYtransSucLp L hL hgn hunL hmI hf
      rw [hsuc] at hidx
      have hdEq : (fList L)^[indexf (lYSpine L (rtransSpine L N r x i) x) d
            (findFaceDarts L (lYSpine L (rtransSpine L N r x i) x))]
          (lYSpine L (rtransSpine L N r x i) x) = d := by
        rw [fListPowEqNextElPow L hL _ hyf]
        exact indexfN hyf hdf hfnd
      have hnm := fListPowYtransNotMem L hL hmI
        (indexf (lYSpine L (rtransSpine L N r x i) x) d
          (findFaceDarts L (lYSpine L (rtransSpine L N r x i) x)) - 1) (by omega)
      rw [show indexf (lYSpine L (rtransSpine L N r x i) x) d
            (findFaceDarts L (lYSpine L (rtransSpine L N r x i) x)) - 1 + 1
          = indexf (lYSpine L (rtransSpine L N r x i) x) d
            (findFaceDarts L (lYSpine L (rtransSpine L N r x i) x)) from by omega,
        hdEq] at hnm
      exact hnm hd
  · -- ⇐：indexf_n 两次 + 位置三分
    intro hle
    rw [hsplit]
    have hN := indexfN hz1 hd hrnd1
    have hNy := indexfN hz1 hy1 hrnd1
    by_cases hp : 0 < indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
        d (rtransSpine L N r x i)
      ∧ indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x) d
          (rtransSpine L N r x i)
        < indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
            (lYSpine L (rtransSpine L N r x i) x) (rtransSpine L N r x i)
    · exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (hbt.mpr hp)))
    · rcases Nat.eq_zero_or_pos (indexf (lZSpine L (ntransSpine L N r x i)
          (rtransSpine L N r x i) x) d (rtransSpine L N r x i)) with h0 | hpos
      · -- idx d = 0 ⇒ d = l'z
        rw [h0] at hN
        have hdz : d = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x :=
          hN.symm
        rw [hdz]
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_singleton.mpr rfl)))
      · -- idx d = idx l'y ⇒ d = l'y
        have heq : indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
            d (rtransSpine L N r x i)
          = indexf (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x)
              (lYSpine L (rtransSpine L N r x i) x) (rtransSpine L N r x i) := by
          omega
        rw [heq, hNy] at hN
        rw [← hN]
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_singleton.mpr rfl))

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.TameSpine.pwssratSpine
