/-
  Kepler.Text.TameSpine.Reduction3KbwpbhqNtrans — tame-corr N-B 段第一批：
  KBWPBHQ 障碍层 spine 消费件（not_in_ntrans_i + CASES1）+ Qcdvkea.FINAL_LIST_INDUCT
  的 spine 镜像。

  ┌─ 归属对账 ────────────────────────────────────────────────────
  │ §0 塔层记号 `ytransSpine`/`ztransSpine`（tame_defs2.hl:475-479 的
  │    spine 载体，定义级 = lYSpine/lZSpine 复合）。
  │ §1 `notInNtrans`（HOL KBWPBHQ.hl:555 `not_in_ntrans_i`）：
  │    indexf w d f < indexf w (ztrans i) f ∧ indexf w (ytrans i) f <
  │    indexf w d f ∧ MEM d f ⇒ ¬MEM d (flatten (ntrans i))。
  │    证体消费（全部在库，spine 世界零混合）：
  │    aqiunpp3（TameList17）· aq10_memNextMarkInface（Leaf10）·
  │    pplhuljV0（ZIndexf §5）· findFaceDarts_congr_of_mem/nodup（TameLp）·
  │    indexfAddLeft/indexfN（TameList3）· indexfYtransSucLp（ZIndexf §3，
  │    塔层 i 直投）· fListPowYtransNotMem（ZIndexf §2，塔层 i 直投）·
  │    fListPowEqNextElPow（ZIndexf §0）。
  │ §2 `cases1`（HOL KBWPBHQ.hl:598 `CASES1`）：结论 ¬MEM d r——
  │    notInNtrans + DANGEYJ（TameList72）+ AQIUNPP3（塔层 0）三步，
  │    与 HOL 同构（r ∈ flatten (ntrans 0) 经 marked_list 合取 3 定义级）。
  │ §3 `finalListInductSpine`（HOL Qcdvkea.hl:46 `FINAL_LIST_INDUCT` 的
  │    spine 镜像）：final 态 transform 恒等 ⇒ 定义级一步，前提子集
  │    （更强形，免 TAV2/marked——与链侧 Reduction5Qcdvkea.finalListInduct
  │    同口径，见该文件头 DIFFERS）。
  │ §4 冻结段（CASES2/PNXVWFS2）前端叶子直投两件：
  │    `memZtransRtransSpine`（mem_ztrans_rtrans 塔层 i 形 =
  │    zMemRtransClean + 塔层 i AQIUNPP3）与 `nextMarkMemRTransSpine`
  │    （next_mark_mem_r_trans 塔层 i 形 = aq10_nextMarkMemRTrans 直投）。
  │    MEM_POWER_NEXT_EL 公开形已在 JcajyduBetwnBase.memPowerNextEl，
  │    查重免重落。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账 ────────────────────────────────────────────────
  │ 全件 spine 世界（ℕ × ℕ，MarkedListSpineFull 载体）——与消费方
  │ DANGEYJ/AQIUNPP3/transformCountSpineNot（TameList72/17、
  │ Reduction3LnrxInductionSpine）同世界零混合；泛 α 列表小件
  │ （indexfN/indexfAddLeft 等，[BEq][LawfulBEq] 泛形）在 ℕ × ℕ 实例化，
  │ 无 Dart-default vs ofDecidableEq BEq 实例碰撞面（R1 记账：本文件
  │ 不含任何 Dart 载体件）。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.TameList72
import Kepler.Text.TameSpine.JcajyduAqLeaf10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face findFaceDarts_nodup
  findFaceDarts_congr_of_mem mem_darts_of_mem_findFace)

/-! ## §0 塔层记号：ytrans / ztrans 的 spine 载体 -/

/-- **HOL `ytrans`**（tame_defs2.hl:475-476）的 spine 载体：
`ytrans L N r x i = l'y L (rtrans L N r x i) x`。 -/
noncomputable def ytransSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (i : ℕ) : ℕ × ℕ :=
  lYSpine L (rtransSpine L N r x i) x

/-- **HOL `ztrans`**（tame_defs2.hl:478-479）的 spine 载体：
`ztrans L N r x i = l'z L (ntrans L N r x i) (rtrans L N r x i) x`。 -/
noncomputable def ztransSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (i : ℕ) : ℕ × ℕ :=
  lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x

/-! ## §1 not_in_ntrans_i（KBWPBHQ.hl:555） -/

/-- **HOL `not_in_ntrans_i`**（KBWPBHQ.hl:555）：
`transform_assumption_v2 ∧ good_list ∧ good_list_nodes ∧ marked_list ∧
find_face x = f ∧ next_el f x = w ∧ ¬final_list (rtrans i) ∧
indexf w d f < indexf w (ztrans i) f ∧ indexf w (ytrans i) f < indexf w d f ∧
MEM d f ⇒ ¬MEM d (flatten (ntrans i))`。

证体与 HOL 同构：PPLHULJ（塔层 i）给 y′, z′ ∈ f 与 w→y′ < w→z′；
`indexf_add_left` 把 w→d 与 w→z′ 劈出 y′→d < y′→z′ 与 0 < y′→d；
`indexf_ytrans_suc_lp`（塔层 i，face 表经 congr 换元到 f）给
y′→z′ = SUC l'p；于是 PRE (y′→d) < l'p；另一侧 `indexf_n` + fList 幂
一致给 d = f^(y′→d) y′，与 d ∈ flatten (ntrans i) 合取即
(k-1) ∈ {p | f^(p+1) y′ ∈ flatten (ntrans i)}，l'p 的 min_num 极小性
（sInf 直投，即 HOL `f_list_power_ytrans_not_mem_ntrans` 的 flatten 形）
给 l'p ≤ k-1，矛盾。 -/
theorem notInNtrans (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {i : ℕ} (hfin : ¬ finalListSpine L (rtransSpine L N r x i))
    {d : ℕ × ℕ}
    (h1 : indexf w d f < indexf w (ztransSpine L N r x i) f)
    (h2 : indexf w (ytransSpine L N r x i) f < indexf w d f)
    (hd : d ∈ f) :
    d ∉ (ntransSpine L N r x i).flatten := by
  -- 记号落位：ytransSpine/ztransSpine 定义级 = lYSpine/lZSpine 复合
  rw [show ztransSpine L N r x i
      = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x from rfl] at h1
  rw [show ytransSpine L N r x i = lYSpine L (rtransSpine L N r x i) x from rfl] at h2
  -- 塔层 i 的标记件（AQIUNPP3）与 face 几何
  have hmr : MarkedListSpineFull hL (ntransSpine L N r x i) (rtransSpine L N r x i) x :=
    aqiunpp3 L hL i hta hgn hm
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hxL : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxf : x ∈ f := hfind ▸ (dart_in_face L x).mpr hxL
  have hwf : w ∈ f := by
    have hw0 := aq10_memNextMarkInface L hL hgn hm
    rw [hfind, hw] at hw0
    exact hw0
  -- PPLHULJ（塔层 i）：y′ ∈ f ∧ z′ ∈ f ∧ w→y′ < w→z′
  have hpl := pplhuljV0 L hL hgn hunL hmr hfin
  obtain ⟨hyf0, hzf0, hlt0⟩ := hpl
  -- l'y 处 face 表与 x 处一致（mem_find_face_imp_faces_eq；用换元前的形态）
  have hcongr : findFaceDarts L (lYSpine L (rtransSpine L N r x i) x)
      = findFaceDarts L x :=
    findFaceDarts_congr_of_mem hL.1 hxL hyf0
  have hyiL : lYSpine L (rtransSpine L N r x i) x ∈ listOfDarts L :=
    mem_darts_of_mem_findFace L hyf0
  have hyiF : lYSpine L (rtransSpine L N r x i) x
      ∈ findFaceDarts L (lYSpine L (rtransSpine L N r x i) x) :=
    (dart_in_face L _).mpr hyiL
  rw [hfind] at hyf0 hzf0
  rw [hfind, hw] at hlt0
  -- face 表唯一（findFaceDarts L x = f 换元）
  have hfnd : f.Nodup := hfind ▸ findFaceDarts_nodup hL.1 x
  -- indexf_add_left：w→y′ 前缀劈开 w→d 与 w→z′
  have had1 := indexfAddLeft hwf hyf0 hd (Nat.le_of_lt h2)
  have had2 := indexfAddLeft hwf hyf0 hzf0 (Nat.le_of_lt hlt0)
  -- 算术：y′→d < y′→z′ ∧ 0 < y′→d
  have hsub1 : indexf (lYSpine L (rtransSpine L N r x i) x) d f
      < indexf (lYSpine L (rtransSpine L N r x i) x)
          (lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x) f := by
    omega
  have hsub2 : 0 < indexf (lYSpine L (rtransSpine L N r x i) x) d f := by
    omega
  -- indexf_ytrans_suc_lp（塔层 i）+ face 表换元到 f：y′→z′ = SUC l'p
  have hsuc := indexfYtransSucLp L hL hgn hunL hmr hfin
  rw [hcongr, hfind] at hsuc
  -- PRE (y′→d) < l'p
  have hpre : indexf (lYSpine L (rtransSpine L N r x i) x) d f - 1
      < lPSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x := by omega
  -- indexf_n：d = (nextEl f)^[y′→d] (l'y)
  have hidx : (nextEl f)^[indexf (lYSpine L (rtransSpine L N r x i) x) d f]
      (lYSpine L (rtransSpine L N r x i) x) = d :=
    indexfN hyf0 hd hfnd
  -- fList 幂一致 + face 表 congr：d = f^[y′→d] (l'y)
  have hpow : (fList L)^[indexf (lYSpine L (rtransSpine L N r x i) x) d f]
      (lYSpine L (rtransSpine L N r x i) x) = d := by
    rw [fListPowEqNextElPow L hL _ hyiF _, hcongr, hfind]
    exact hidx
  -- 收口：d = f^[k] (l'y)（k := y′→d）与 d ∈ flatten (ntrans i) ⇒
  -- (k-1) ∈ {p | f^[p+1] (l'y) ∈ flatten (ntrans i)} ⇒ l'p ≤ k-1，与 hpre 矛盾
  -- （l'p 极小性即 HOL f_list_power_ytrans_not_mem_ntrans 的 flatten 形）
  intro hmem
  have heq : indexf (lYSpine L (rtransSpine L N r x i) x) d f - 1 + 1
      = indexf (lYSpine L (rtransSpine L N r x i) x) d f :=
    Nat.sub_add_cancel hsub2
  have hmem' : (fList L)^[indexf (lYSpine L (rtransSpine L N r x i) x) d f]
        (lYSpine L (rtransSpine L N r x i) x)
      ∈ (ntransSpine L N r x i).flatten := by
    rw [hpow]
    exact hmem
  have hmem'' : (fList L)^[indexf (lYSpine L (rtransSpine L N r x i) x) d f - 1 + 1]
        (lYSpine L (rtransSpine L N r x i) x)
      ∈ (ntransSpine L N r x i).flatten := by
    rw [heq]
    exact hmem'
  have hle : lPSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
      ≤ indexf (lYSpine L (rtransSpine L N r x i) x) d f - 1 :=
    Nat.sInf_le hmem''
  omega

/-! ## §2 CASES1（KBWPBHQ.hl:598） -/

/-- **HOL `CASES1`**（KBWPBHQ.hl:598）：同 `notInNtrans` 前件 ⇒ `¬MEM d r`。
证体与 HOL 同构三步：notInNtrans 给 ¬MEM d (flatten (ntrans i))；
DANGEYJ 给 flatten (ntrans 0) ⊆ flatten (ntrans i)（0 ≤ i）；塔层 0 的
AQIUNPP3 合取 3 给 r ∈ ntrans 0（= N 定义级），d ∈ r 即 d ∈ flatten (ntrans 0)。 -/
theorem cases1 (L : fgraph ℕ) (hL : GoodList L)
    (hta : transformAssumptionSpine L hL) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x)
    {f : List (ℕ × ℕ)} {w : ℕ × ℕ}
    (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {i : ℕ} (hfin : ¬ finalListSpine L (rtransSpine L N r x i))
    {d : ℕ × ℕ}
    (h1 : indexf w d f < indexf w (ztransSpine L N r x i) f)
    (h2 : indexf w (ytransSpine L N r x i) f < indexf w d f)
    (hd : d ∈ f) :
    d ∉ r := by
  intro hmem
  have hnt := notInNtrans L hL hta hgn hunL hm hfind hw hfin h1 h2 hd
  refine hnt ?_
  have hm0 : MarkedListSpineFull hL (ntransSpine L N r x 0) (rtransSpine L N r x 0) x :=
    aqiunpp3 L hL 0 hta hgn hm
  have hsub := DANGEYJ L hL hta hgn N r x 0 i hm (Nat.zero_le i)
  refine hsub ?_
  exact List.mem_flatten.mpr ⟨rtransSpine L N r x 0, hm0.1.2.2.1, hmem⟩

/-! ## §3 FINAL_LIST_INDUCT 的 spine 镜像（Qcdvkea.hl:46） -/

/-- **HOL `Qcdvkea.FINAL_LIST_INDUCT`**（Qcdvkea.hl:46）的 spine 镜像：
`¬final_list (rtrans (SUC i)) ⇒ ¬final_list (rtrans i)`——final 态
transform 恒等，定义级一步。前提子集（更强形，免 TAV2/marked），与链侧
`Kepler.Text.Reduction5.finalListInduct` 同口径（见 Reduction5Qcdvkea
文件头 DIFFERS）；消费者携全前提时直接可喂。 -/
theorem finalListInductSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x (i + 1))) :
    ¬ finalListSpine L (rtransSpine L N r x i) := by
  intro hfin
  refine hf ?_
  have hc : finalListSpine L ((transformListSpine L x)^[i] (N, r)).2 := hfin
  have hstep : rtransSpine L N r x (i + 1) = rtransSpine L N r x i := by
    show ((transformListSpine L x)^[i + 1] (N, r)).2
        = ((transformListSpine L x)^[i] (N, r)).2
    rw [Function.iterate_succ_apply']
    simp only [transformListSpine]
    rw [if_pos hc]
  rw [hstep]
  exact hfin

/-! ## §4 冻结段（CASES2 / pnxvwfs2）前端叶子直投两件 -/

/-- **HOL `mem_ztrans_rtrans`**（PWSSRAT 章通用形，KBWPBHQ/CASES2/PNXVWFS2
消费面）的 spine 载体、塔层 i 形：`MEM (ztrans L N r x i) (rtrans L N r x i)`。
证 = `zMemRtransClean`（JcajyduAqZUnlock，l'z ∈ r 干净形）在塔层 (ni, ri)
直投，标记件由塔层 i 的 AQIUNPP3 供给。 -/
theorem memZtransRtransSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    (hta : transformAssumptionSpine L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ)
    (hf : ¬ finalListSpine L (rtransSpine L N r x i)) :
    lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
      ∈ rtransSpine L N r x i :=
  zMemRtransClean L hL hgn hunL (aqiunpp3 L hL i hta hgn hm) hf

/-- **HOL `Ncvibwu.next_mark_mem_r_trans`**（NCVIBWU.hl:302）的 spine 载体、
塔层 i 形：`MEM w (rtrans L N r x i)`（w = next_el (find_face x) x）。
证 = `aq10_nextMarkMemRTrans` 在塔层 (ni, ri) 直投（标记件由塔层 i
AQIUNPP3 供给）；更强形（免 ¬final 前提，与 finalListInductSpine 同口径）。 -/
theorem nextMarkMemRTransSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hta : transformAssumptionSpine L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (i : ℕ) :
    nextEl (findFaceDarts L x) x ∈ rtransSpine L N r x i :=
  aq10_nextMarkMemRTrans L hL hgn (aqiunpp3 L hL i hta hgn hm)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.ytransSpine
#print axioms Kepler.Text.TameSpine.ztransSpine
#print axioms Kepler.Text.TameSpine.notInNtrans
#print axioms Kepler.Text.TameSpine.cases1
#print axioms Kepler.Text.TameSpine.finalListInductSpine
#print axioms Kepler.Text.TameSpine.memZtransRtransSpine
#print axioms Kepler.Text.TameSpine.nextMarkMemRTransSpine
