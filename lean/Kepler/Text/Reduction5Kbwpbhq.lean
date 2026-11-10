/-
  Kepler.Text.Reduction5Kbwpbhq — W2-c-3：KBWPBHQ2 支撑波三件链孪生
  （`mem_ytrans_list_of_darts` HOJODCM.hl / `prev_el_betwn_ztran_rtrans`
  KBWPBHQ.hl / `Nuxcoea.MIN_LEAST` local/NUXCOEA.hl）。

  ┌─ 路线（链侧；零 TameSpine import）────────────────────────────
  │ ① `memYtransListOfDarts`：HOL 走 marked_list 展开 + HQYMRTX1_list；
  │    链侧利用 `ly = (f_list)^(l'm+1)` 的 **rfl 定义** + f_list 迭代成员
  │    闭包（`TameLp.fList_mem_darts`）直证——免 HQYMRTX1 链侧化。
  │ ② `prevElBetwnZtranRtrans`：HOL 的 change_next_prev/MEM_POWER/
  │    indexf_n/indexf_lt_sizel/next_eln_indexf 五引路线，链侧对应
  │    `prevEl_nextEl` / `memNextElIterate` / `indexfN`（隔位迭代等式）/
  │    `indexf_lt_length_of_mem` / `nextElnIndexf`，算术全交 omega；
  │    主不等式 = `indexfYLeZInR0` 在 (ntrans i, rtrans i) 状态实例化。
  │ ③ `minLeast`：`Reduction5.minNum_spec` 直投。
  └────────────────────────────────────────────────────────────────

  **纪律**：零占位证明、零新增公理、零反射式判定；主仓双零写入。禁词零。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.Reduction5
import Kepler.Text.ChainListsL2
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.Reduction4Subseg9
import Kepler.Text.PwssratMemberBase
import Kepler.Text.PwssratCase
import Kepler.Text.TameLp

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl prevEl fList listOfDarts findFaceDarts)


/-! ## §0 跨实例 `nextEl` 桥簇（雷区⑪ 修复形；陈述形状 = **逐点等式**）

链上两族引理的 `nextEl` 在声明时烤死了不同实例：Island1 系
（`indexfN`/`memNextElIterate`/`nextElnIndexf`）烤 `instBEqOfDecidableEq`，
TameLp 系（`prevEl_nextEl`）与本文件默认烤 `instBEqProd`。两实例非 defeq
（`LawfulBEq` 只保证行为相等）。桥簇提供 **逐点等式**（非 `List.Index` 级）：

① `findIdxBeqAgree`：判定函数点态一致 ⇒ `findIdx` 相等；
② `beqProdDerivedEq`：两实例的 `beq` 逐点相等（都 = `decide (b = a)`）；
③ `idxOfInstEq`：`@List.idxOf Dart instBEqProd = @List.idxOf Dart instBEqOfDecidableEq`
   （逐元素等式形）；
④ `nextElInstEq` / `iterateInstEq`：`nextEl` 及任意次迭代的逐点等式。
共享说明：aq13 主山 NCVIBWU 若也用 Island1 系引理，可复用 ①–④（同一陈述形状）。 -/

/-- 判定函数点态一致 ⇒ `findIdx` 相等。 -/
theorem findIdxBeqAgree {p q : Dart → Bool} (h : ∀ a, p a = q a) :
    ∀ xs : List Dart, List.findIdx p xs = List.findIdx q xs
  | [] => rfl
  | a :: t => by
    rw [List.findIdx_cons, List.findIdx_cons, h a, findIdxBeqAgree h t]

/-- 两实例 `beq` 逐点相等：`@BEq.beq Dart instBEqProd b a = @BEq.beq Dart
instBEqOfDecidableEq b a`。 -/
theorem beqProdDerivedEq (b a : Dart) :
    @BEq.beq Dart instBEqProd b a = @BEq.beq Dart instBEqOfDecidableEq b a := by
  have h2 : @BEq.beq Dart instBEqOfDecidableEq b a = decide (b = a) := rfl
  rw [h2]
  by_cases h : b = a
  · have h1 : @BEq.beq Dart instBEqProd b a = true :=
      (@beq_iff_eq Dart instBEqProd _ b a).mpr h
    rw [h1]
    exact (decide_eq_true h).symm
  · have h1 : @BEq.beq Dart instBEqProd b a = false :=
      (@beq_eq_false_iff_ne Dart instBEqProd _ b a).mpr h
    have hd : decide (b = a) = false := decide_eq_false_iff_not.mpr h
    rw [h1, hd]

/-- `idxOf` 跨实例逐元素等式。 -/
theorem idxOfInstEq (a : Dart) (s : List Dart) :
    @List.idxOf Dart instBEqProd a s = @List.idxOf Dart instBEqOfDecidableEq a s := by
  unfold List.idxOf
  exact findIdxBeqAgree (fun b => beqProdDerivedEq b a) s

/-- `nextEl` 跨实例逐点等式。 -/
theorem nextElInstEq (s : List Dart) (x : Dart) :
    @nextEl Dart instBEqProd s x = @nextEl Dart instBEqOfDecidableEq s x := by
  unfold Kepler.Assembly.nextEl
  rw [idxOfInstEq x s]

/-- `nextEl` 迭代跨实例逐点等式。 -/
theorem iterateInstEq (s : List Dart) (x : Dart) :
    ∀ n, (@nextEl Dart instBEqProd s)^[n] x
      = (@nextEl Dart instBEqOfDecidableEq s)^[n] x
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      iterateInstEq s x n,
      nextElInstEq s ((@nextEl Dart instBEqOfDecidableEq s)^[n] x)]

/-! ## §1 `Nuxcoea.MIN_LEAST`（local/NUXCOEA.hl：`c ∈ X ⇒ min_num X ∈ X ∧ min_num X ≤ c`） -/

/-- **HOL `Nuxcoea.MIN_LEAST`**：`minNum_spec` 直投。 -/
theorem minLeast {X : Set ℕ} {c : ℕ} (hc : c ∈ X) :
    Kepler.Text.Reduction5.minNum X ∈ X ∧ Kepler.Text.Reduction5.minNum X ≤ c := by
  obtain ⟨h1, h2⟩ := Kepler.Text.Reduction5.minNum_spec ⟨c, hc⟩
  exact ⟨h1, h2 c hc⟩

/-! ## §2 `mem_ytrans_list_of_darts`（HOJODCM.hl） -/

/-- f_list 迭代成员闭包。 -/
private theorem fListIterateDarts {L : fgraph ℕ} (hn : (listOfDarts L).Nodup) {d : Dart}
    (hd : d ∈ listOfDarts L) : ∀ m, (fList L)^[m] d ∈ listOfDarts L := by
  intro m
  induction m with
  | zero => simpa using hd
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact Kepler.Text.TameLp.fList_mem_darts hn ih

/-- **HOL `Hojodcm.mem_ytrans_list_of_darts`**（HOJODCM.hl，v0 形）：`good_list ∧
good_list_nodes ∧ marked_list L N r x ∧ ¬final_list L r ⇒
MEM (ytrans L N r x 0) (list_of_darts L)`。 -/
theorem memYtransListOfDarts {L : fgraph ℕ} {N : List (List Dart)} {r : List Dart}
    {x : Dart} (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    ytrans L N r x 0 ∈ listOfDarts L := by
  have hx : x ∈ listOfDarts L := Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm
  have hy_eq : ytrans L N r x 0 = Kepler.Text.Reduction5.ly L r x := by
    simp [Kepler.Text.Reduction5.ytrans, Kepler.Text.Reduction5.rtrans_zero]
  have hly : Kepler.Text.Reduction5.ly L r x
      = (fList L)^[Kepler.Text.Reduction5.lm L r x + 1] x := rfl
  rw [hy_eq, hly]
  exact fListIterateDarts hL.1 hx _

/-! ## §3 `prev_el_betwn_ztran_rtrans`（KBWPBHQ.hl）

实例记账（pp.all 实测）：`indexfYLeZInR0` 的 `nextEl` = **prod-of-derived-Nat 变体**
`@instBEqProd Nat Nat (instBEqOfDecidableEq Nat _) (instBEqOfDecidableEq Nat _)`
——与**本文件裸名合成同类**（下称 P）；Island1 系泛型 `[DecidableEq]` 实例化所得为
`instBEqOfDecidableEq (instDecidableEqProd …)`（下称 D）。桥簇 `iterateInstEq`
（P = D，逐点）负责两向转换。 -/

/-- **HOL `Kbwpbhq.prev_el_betwn_ztran_rtrans`**（KBWPBHQ.hl）：在 `(rtrans i)` 上
`prev_el zi` 落在 `yi` 与 `zi` 之间的三合取（成员 / 严格小于 zi / ≥ yi）。
TAV2 前提按 Pwssrat 簇惯例以 `AqiunppSlot` 显式槽供给。 -/
theorem prevElBetwnZtranRtrans {L : fgraph ℕ} {N : List (List Dart)}
    {r : List Dart} {x : Dart} (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) {i : ℕ}
    (hf : ¬ finalList L (rtrans L N r x i))
    {w : Dart} (hw : nextEl (findFaceDarts L x) x = w) :
    prevEl (rtrans L N r x i) (ztrans L N r x i) ∈ rtrans L N r x i ∧
    indexf w (prevEl (rtrans L N r x i) (ztrans L N r x i)) (rtrans L N r x i)
      < indexf w (ztrans L N r x i) (rtrans L N r x i) ∧
    indexf w (ytrans L N r x i) (rtrans L N r x i)
      ≤ indexf w (prevEl (rtrans L N r x i) (ztrans L N r x i)) (rtrans L N r x i) := by
  set ri := rtrans L N r x i with hri
  have hm' : Kepler.Text.ChainLists.markedList L hL (ntrans L N r x i) ri x :=
    haq hgn N r x hm i
  have hrnd : ri.Nodup := (List.nodup_flatten.mp hm'.2.1.1).1 ri hm'.2.2.1
  -- 三成员
  have hmem_z : ztrans L N r x i ∈ ri :=
    Kepler.Text.Reduction4Idx.memZtransRtrans L hL haq hgn hunL i hm hf
  have hmem_y : ytrans L N r x i ∈ ri :=
    Kepler.Text.MoreLemma2Naming.ytransMemRtrans L hL hm' hf
  have hmem_w : w ∈ ri :=
    Kepler.Text.Reduction4Idx.nextMarkMemRTrans L hL haq hgn i hm rfl hw
  -- 主不等式：h0 已在 P（与裸名同类）⇒ 直接换 w 与 ytrans/ztrans 定义
  have hyz : indexf w (ytrans L N r x i) ri < indexf w (ztrans L N r x i) ri := by
    have h0 := Kepler.Text.Reduction4Idx.indexfYLeZInR0 L hL hgn hunL hm' hf
    rw [hw] at h0
    simpa [Kepler.Text.Reduction5.ytrans, Kepler.Text.Reduction5.ztrans] using h0
  -- 弧和
  have hadd : indexf w (ytrans L N r x i) ri + indexf (ytrans L N r x i)
      (ztrans L N r x i) ri = indexf w (ztrans L N r x i) ri :=
    Kepler.Text.Reduction4.indexf_add_left hmem_w hmem_y hmem_z (le_of_lt hyz)
  have hm_pos : 0 < indexf (ytrans L N r x i) (ztrans L N r x i) ri := by omega
  -- 迭代分解（Island1 = D → 桥转 P）：zi = (nextEl ri)^(m) yi
  have hiter : (nextEl ri)^[
      indexf (ytrans L N r x i) (ztrans L N r x i) ri] (ytrans L N r x i)
      = ztrans L N r x i := by
    have h0 := Kepler.Text.MoreLemma2Island1.indexfN hmem_y hmem_z hrnd
    rwa [← iterateInstEq] at h0
  -- n = m - 1；prevEl zi = (nextEl)^n yi（TameLp.prevEl_nextEl 同在 P）
  have hsucc' : (indexf (ytrans L N r x i) (ztrans L N r x i) ri - 1).succ
      = indexf (ytrans L N r x i) (ztrans L N r x i) ri :=
    Nat.succ_pred_eq_of_pos hm_pos
  have hz_pre : ztrans L N r x i
      = nextEl ri ((nextEl ri)^[indexf (ytrans L N r x i)
          (ztrans L N r x i) ri - 1] (ytrans L N r x i)) := by
    rw [← Function.iterate_succ_apply' (nextEl ri)
      (indexf (ytrans L N r x i) (ztrans L N r x i) ri - 1) (ytrans L N r x i)]
    rw [hsucc']
    exact hiter.symm
  have hd_mem : (nextEl ri)^[indexf (ytrans L N r x i) (ztrans L N r x i) ri - 1]
      (ytrans L N r x i) ∈ ri := by
    have h0 := Kepler.Text.MoreLemma2Island1.memNextElIterate hmem_y
      (indexf (ytrans L N r x i) (ztrans L N r x i) ri - 1)
    rwa [← iterateInstEq] at h0
  have hprev : prevEl ri (ztrans L N r x i)
      = (nextEl ri)^[indexf (ytrans L N r x i) (ztrans L N r x i) ri - 1]
          (ytrans L N r x i) := by
    conv_lhs => rw [hz_pre]
    exact Kepler.Text.TameLp.prevEl_nextEl hrnd hd_mem
  -- indexf w d = (m-1) + indexf w yi（nextElnIndexf = D；两侧入参/出参各转一次）
  have hwi : (nextEl ri)^[indexf w (ytrans L N r x i) ri] w = ytrans L N r x i := by
    have h0 := Kepler.Text.MoreLemma2Island1.indexfN hmem_w hmem_y hrnd
    rwa [← iterateInstEq] at h0
  have hwiter : (nextEl ri)^[(indexf (ytrans L N r x i) (ztrans L N r x i) ri - 1)
        + indexf w (ytrans L N r x i) ri] w
      = (nextEl ri)^[indexf (ytrans L N r x i) (ztrans L N r x i) ri - 1]
          (ytrans L N r x i) := by
    rw [Function.iterate_add_apply, hwi]
  have hcidx : indexf w (ztrans L N r x i) ri < ri.length :=
    Kepler.Text.Reduction4.indexf_lt_length_of_mem hmem_w hmem_z
  have hclen : (indexf (ytrans L N r x i) (ztrans L N r x i) ri - 1)
      + indexf w (ytrans L N r x i) ri < ri.length := by omega
  have hidx_d : indexf w ((nextEl ri)^[indexf (ytrans L N r x i)
        (ztrans L N r x i) ri - 1] (ytrans L N r x i)) ri
      = (indexf (ytrans L N r x i) (ztrans L N r x i) ri - 1)
        + indexf w (ytrans L N r x i) ri := by
    have hdD := hd_mem
    rw [iterateInstEq] at hdD
    have hwD := hwiter
    rw [iterateInstEq] at hwD
    rw [iterateInstEq] at hwD
    have h0 := Kepler.Text.MoreLemma2Island1.nextElnIndexf hmem_w hdD hrnd hwD hclen
    rwa [← iterateInstEq] at h0
  refine ⟨hprev ▸ Kepler.Text.TameLp.prevEl_mem_of_mem hmem_z, ?_, ?_⟩
  · rw [hprev, hidx_d]
    omega
  · rw [hprev, hidx_d]
    omega

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三） -/
#print axioms Kepler.Text.Reduction5.minLeast
#print axioms Kepler.Text.Reduction5.memYtransListOfDarts
#print axioms Kepler.Text.Reduction5.prevElBetwnZtranRtrans
