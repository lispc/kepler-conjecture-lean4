/-
  Kepler.Text.TameSpine.JcajyduAqTowerE2 — jcajydu J2 批 E-2：AQ2/AQ3（AQ23.hl）
  第一口 —— **AQ2 真证落定**（normal_list 合取 2 槽补全，塔 13 叶第 2 叶）+
  AQ3 split.2 支的三槽条件形 + betwn/next_el 环回泛型件（E3/E4/E5 共用底）。

  ┌─ E2 现场考古（对 E1 §1.4 预判的修正；机器证据为准）────────────
  │ ① **AQ2 直达路线完全干净**（E1 预判兑现）：final 支 = ntransId +
  │   normal_list 合取 2；¬final 支 = ntrans1 展开 + E1 memReplaceCases
  │   双源分解（s ∈ N 用合取 2；s = split.2/split.1 由 cons 结构平凡非空）。
  │   HOL AQ2 证明（AQ23.hl:46-:91）装载的 z_not_eq_ytrans_v0 等 7 件
  │   上下文零消费——「上下文装载 ≠ 实质依赖」模式第二例（E1 §1.5-3）。
  │ ② **AQ3 修正**：HOL next_el_cat_last2（tame_list.hl:5665-:5681）实为
  │   **环回头件** `next_el (cat s t) (LAST t) = HD s`（非段一致件），
  │   split.2 案两支的 f 侧都需要 `z ∈ face(y)`（空窗支经 exist_or_next_f
  │   (AQ23.hl:96) ← PPLHULJ_v0 + z_not_eq_ytrans_v0 债链；非空窗支经
  │   next_last_betwn 的 MEM z face）——加上 LHS 侧 uniq split.2，AQ3
  │   split.2 的干净条件形挂 **3 槽**（y≠z〔hqymrtx3 债〕、z∈face
  │   〔HOJODCM:179 ztran_in_face 债链〕、split.2.Nodup〔uniq_snd_split_
  │   norm AQ1:413 零命中〕），本批以 aq3Split2FLast 条件形落定（§2）。
  │ ③ **AQ3-split1 案 BLOCKED**（AQ23.hl:359-:502）：f_last (split.1) 的
  │   证词 = uniq_fst_split_norm（AQ1:1373 零命中）+ Hypermap
  │   lemma_node_cycle/lemma_node_nondegenerate + Lebhirj
  │   n_list_ext_n_list_power（×19 零命中）+ Hojodcm.count_node_face
  │   （×40 零命中）+ Tame_list.dart_of_card_node + Lp_gen_theory
  │   dart_list_all——n_list 幂循环机自成子塔，归 E4/E5，不在 E2 硬凑。
  └────────────────────────────────────────────────────────────────

  ┌─ 债务隔离 ─────────────────────────────────────────────────────
  │ 零消费 TameList16:1109 在案 sorryAx 债链（hqymrtx1-3List/
  │ markedListMarked/markedTranslate 零引用）；hyne/hzface/hsnd 以显式
  │ 槽参数挂账（AGENTS §2：不许绕假桩凑证——挂槽即诚实记账）。
  │ TameList17:93 off-by-one：本批与 E1 同边界（ntrans1/split.2 支陈述
  │ 对 nd 值不敏感），零内容级消费 splitNormalListSpine.split.1。
  │ 泛型 binder：betwn/next_el 件沿 JcajyduBetwnBase 三例随形
  │ （[BEq α][LawfulBEq α][DecidableEq α]，α=ℕ×ℕ 处吃 instBEqProd）。
  └────────────────────────────────────────────────────────────────

  纪律：零 sorry/admit/native_decide/axiom 声明；既有文件零触碰；主仓
  tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.TameSpine.TameList17
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.JcajyduBetwnBase
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.TameSpine.JcajyduAqTowerBase

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl eList fList GoodList findFaceDarts nList
  listOfDarts)
open Kepler.Graphs (fgraph between splitAt)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  nextEl_eq_getD getD_eq_getElem_of_lt)

/-! ## §0 betwn/next_el 环回泛型件（E3/E4/E5 共用底）

HOL 锚：next_el_cat_last2（tame_list.hl:5665）、betwn_mem（Tame_list）、
exist_or_next_f 的纯列表内核（AQ23.hl:96 的 `(∃d. MEM d (betwn f y z)) ↔
¬(next_el f y = z)` 的空窗方向）。 -/

/-- `s ≠ []` 时 `getLast!` 是成员（TameList12 同证重推导，per-file-private
约定零共享）。 -/
private theorem getLastMem' {α : Type*} [Inhabited α] {s : List α}
    (h : s ≠ []) : s.getLast! ∈ s := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- **HOL `next_el_cat_last2`**（tame_list.hl:5665-:5681）逐句镜像：
`uniq (cat s t) /\ ~(t = []) /\ ~(s = []) ==> next_el (cat s t) (LAST t) =
HD s`——环回头（拼接表的末元下一跳 = 头）。E2 考古修正：此件是环回头
而非段一致件，AQ3/AQ12 的拼接跳转由它承担。 -/
theorem nextElAppendLastOfNodup {α : Type*} [Inhabited α] [BEq α] [LawfulBEq α]
    [DecidableEq α] {s t : List α} (hst : (s ++ t).Nodup) (hs : s ≠ [])
    (ht : t ≠ []) : nextEl (s ++ t) t.getLast! = s.head! := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil s hs
  have hne : s ++ t ≠ [] := mem_imp_not_nil
    (List.mem_append.mpr (Or.inl hw))
  have hgt : t.getLast! = (s ++ t).getLast hne := by
    rw [List.getLast_append_of_right_ne_nil s t ht, getLast!EqGetLast ht]
  rw [hgt, nextElLastHd hst hne]
  exact List.head!_append t hs

/-- **HOL `Tame_list.betwn_mem`**（betwn 的落点内含性）：`MEM d (betwn r y z)
==> MEM d r`——splitAt take/drop 逐支落点。 -/
theorem memBetweenOfMem {α : Type*} [BEq α] [LawfulBEq α] {r : List α}
    {y z w : α} (h : w ∈ between r y z) : w ∈ r := by
  simp only [between, splitAt, splitAtRecTakeDropPair, List.nil_append] at h
  by_cases hcon : (r.drop (r.idxOf y + 1)).contains z
  · rw [if_pos hcon] at h
    exact List.mem_of_mem_drop (List.mem_of_mem_take h)
  · rw [if_neg hcon] at h
    rcases List.mem_append.mp h with h1 | h1
    · exact List.mem_of_mem_drop h1
    · exact List.mem_of_mem_take (List.mem_of_mem_take h1)

/-- **exist_or_next_f 的纯列表内核（空窗方向）**：`uniq r ∧ MEM y r ∧
MEM z r ∧ y ≠ z ∧ betwn r y z = [] ==> next_el r y = z`——AQ3 split.2 空窗
支的 f 侧引擎（HOL 经 exist_or_next_f←PPLHULJ/债链取得的同一事实的干净
泛型化：此处不需要任何 marked_list 内容）。

证：splitAt y r 的 take/drop 两支——直段支（drop 含 z）betwn =
drop.take (drop.idxOf z) = [] ⟹ drop.idxOf z = 0 ⟹ z = drop[0] = r[iy+1]
（iy+1 < len ⟹ nextEl 走 getD 支）；回环支（drop 不含 z）betwn =
drop ++ take.take (take.idxOf z) = [] ⟹ drop = []（y 末位，nextEl 走
head 支）∧ take.idxOf z = 0（z = take 头 = r 头；take ≠ [] 由 z ∈ take ∧
z ≠ y 给出）。 -/
theorem betwnNilNextOfNodup {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α]
    {r : List α} {a b : α} (hnd : r.Nodup) (ha : a ∈ r) (hb : b ∈ r)
    (hab : a ≠ b) (hnil : between r a b = []) : nextEl r a = b := by
  have hlt : r.idxOf a < r.length := List.idxOf_lt_length_iff.mpr ha
  have hcons : r.drop (r.idxOf a) = a :: r.drop (r.idxOf a + 1) := by
    rw [List.drop_eq_getElem_cons hlt, List.getElem_idxOf hlt]
  have hstruct : r.take (r.idxOf a) ++ a :: r.drop (r.idxOf a + 1) = r := by
    rw [← hcons, List.take_append_drop]
  simp only [between, splitAt, splitAtRecTakeDropPair, List.nil_append] at hnil
  by_cases hcon : (r.drop (r.idxOf a + 1)).contains b
  · rw [if_pos hcon] at hnil
    have hpostne : r.drop (r.idxOf a + 1) ≠ [] := by
      intro h0; rw [h0] at hcon; simp at hcon
    have hplt : r.idxOf a + 1 < r.length := by
      have h1 : (r.drop (r.idxOf a + 1)).length = r.length - (r.idxOf a + 1) :=
        List.length_drop
      have h2 : 0 < (r.drop (r.idxOf a + 1)).length :=
        List.length_pos_of_ne_nil hpostne
      omega
    have hk0 : (r.drop (r.idxOf a + 1)).idxOf b = 0 := by
      rcases List.take_eq_nil_iff.mp hnil with hk | hp
      · exact hk
      · rw [hp] at hpostne
        exact absurd hpostne (by simp)
    have hz2 : 0 < (r.drop (r.idxOf a + 1)).length :=
      List.length_pos_of_ne_nil hpostne
    have hb0 : (r.drop (r.idxOf a + 1))[0]'hz2 = b := by
      have hh := (List.idxOf_eq_zero_iff_head_eq hpostne).mp hk0
      rw [List.getElem_zero hz2]
      exact hh
    rw [nextEl_eq_getD ha, Nat.mod_eq_of_lt hplt, getD_eq_getElem_of_lt hplt,
      List.getElem_drop' hplt]
    simp only [hcons]
    exact hb0
  · rw [if_neg hcon] at hnil
    -- append = [] 同时给出两件事：post = []（a 末位）与 pre-take = []（z = take 头）
    have hpd : r.drop (r.idxOf a + 1) = [] := (List.append_eq_nil_iff.mp hnil).1
    have hpt : (r.take (r.idxOf a)).take ((r.take (r.idxOf a)).idxOf b) = [] :=
      (List.append_eq_nil_iff.mp hnil).2
    have hia2 : r.idxOf a = r.length - 1 := by
      have h0 : (r.drop (r.idxOf a + 1)).length = 0 := by rw [hpd]; simp
      have hlen : (r.drop (r.idxOf a + 1)).length
          = r.length - (r.idxOf a + 1) := List.length_drop
      omega
    have hbin : b ∈ r.take (r.idxOf a) ++ a :: r.drop (r.idxOf a + 1) := by
      rw [hstruct]; exact hb
    have hbpre : b ∈ r.take (r.idxOf a) := by
      rcases List.mem_append.mp hbin with hb1 | hb2
      · exact hb1
      · rcases List.mem_cons.mp hb2 with hba | hbp
        · exact absurd hba.symm hab
        · exact absurd (List.contains_iff_mem.mpr hbp :
            (r.drop (r.idxOf a + 1)).contains b) hcon
    have hbne : r.take (r.idxOf a) ≠ [] := by
      intro h0; rw [h0] at hbpre; simp at hbpre
    have hk0 : (r.take (r.idxOf a)).idxOf b = 0 := by
      rcases List.take_eq_nil_iff.mp hpt with hk | hp2
      · exact hk
      · rw [hp2] at hbne
        exact absurd hbne (by simp)
    rw [nextEl_eq_getD ha]
    rw [show (r.idxOf a + 1) % r.length = 0 by
      have h1 : r.idxOf a + 1 = r.length := by omega
      rw [h1, Nat.mod_self]]
    -- goal：r.getD 0 a = b；r = (c :: cs) ++ [a] ⇒ getD 0 = c = b
    obtain ⟨c, cs, hcpre⟩ := List.exists_cons_of_ne_nil hbne
    have hk0' : (c :: cs).idxOf b = 0 := by rw [← hcpre]; exact hk0
    have hbne2 : (c :: cs) ≠ [] := by rw [← hcpre]; exact hbne
    have hb0' : c = b := by
      have hh := (List.idxOf_eq_zero_iff_head_eq hbne2).mp hk0'
      exact hh
    have hreq : r = r.take (r.idxOf a) ++ [a] := by
      rw [← hpd, ← hcons, List.take_append_drop]
    have hrEq : r = c :: cs ++ [a] := by rw [hreq, hcpre]
    rw [hrEq]
    simp
    exact hb0'

/-! ## §1 AQ2 真证（AQ23.hl:39-:91；normal_list 合取 2 槽补全） -/

/-- `splitNormalListSpine` 的 `.1`（new1.reverse ++ f1）非空：f1 以
`[nextEl r ram1]` 的 cons 头平凡非空（零前提，纯结构）。 -/
private theorem split1NeNil (L : fgraph ℕ) (r f : List (ℕ × ℕ))
    (ram1 ram2 : ℕ × ℕ) : (splitNormalListSpine L r f ram1 ram2).1 ≠ [] := by
  simp only [splitNormalListSpine]
  exact mem_imp_not_nil (List.mem_append.mpr (Or.inr
    (List.mem_append.mpr (Or.inl (List.mem_cons_self ..)))))

/-- `splitNormalListSpine` 的 `.2`（f2 ++ new2）非空：f2 以 `[nextEl r ram2]`
的 cons 头平凡非空（零前提，纯结构）。 -/
private theorem split2NeNil (L : fgraph ℕ) (r f : List (ℕ × ℕ))
    (ram1 ram2 : ℕ × ℕ) : (splitNormalListSpine L r f ram1 ram2).2 ≠ [] := by
  simp only [splitNormalListSpine]
  exact mem_imp_not_nil (List.mem_append.mpr (Or.inl
    (List.mem_append.mpr (Or.inl (List.mem_cons_self ..)))))

/-- **HOL `AQ2`**（AQ23.hl:46-:91）真证——`all (\s. ~(s = []))
(ntrans L N r x 1)`，即 `aq2Concl`（E1 §3 陈述槽）的内容补全：normal_list
在 N' = ntrans…1 处的合取 2。final 支 = ntransId + marked_list 的
normal_list 合取 2；¬final 支 = ntrans1 展开 + E1 memReplaceCases 双源
分解 + split.1/split.2 的 cons 结构平凡非空。HOL 的七件上下文装载
（uniq_find_face/marked_list_of_dart/mem_ztrans_rtrans_v0/ytrans_mem_
rtrans_v0/z_not_eq_ytrans_v0/mem_ytrans_list_of_darts_v0/PPLHULJ_v0）
零消费——「上下文装载 ≠ 实质依赖」第二例。 -/
theorem aq2 (L : fgraph ℕ) (hL : GoodList L) : aq2Concl L hL := by
  intro N r x _hgn hm s hs
  by_cases hfin : finalListSpine L r
  · rw [ntransId L N r x hfin] at hs
    exact hm.1.2.1.2.1 s hs
  · rw [ntrans1 L N r x hfin] at hs
    rcases List.mem_append.mp hs with hs1 | hs1
    · rcases memReplaceCases hs1 with hN | ⟨_, hsf2⟩
      · exact hm.1.2.1.2.1 s hN
      · rcases List.mem_cons.mp hsf2 with rfl | h0
        · exact split2NeNil L r (findFaceDarts L (lYSpine L r x))
            (lYSpine L r x) (prevEl r (lZSpine L N r x))
        · exact absurd h0 (by simp)
    · rcases List.mem_cons.mp hs1 with rfl | h0
      · exact split1NeNil L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))
      · exact absurd h0 (by simp)

/-! ## §2 AQ3 split.2 支的三槽条件形（AQ23.hl:311-:352 的干净内核）

**AQ3 全式 BLOCKED 记账**（AGENTS §7，机器证据为准）：
- split.2 支需要三槽——`hyne : l'y ≠ l'z`（HOL z_not_eq_ytrans_v0 ←
  HQYMRTX1_list ← TameList16:1109 在案债）、`hzface : l'z ∈ find_face L y`
  （HOL ztran_in_face_ytrans_v0 ← 同债链）、`hsnd : uniq split.2`
  （HOL uniq_snd_split_norm AQ1:413，零命中）——三槽以显式参数挂账，
  填证属 E3；
- split.1 支（f_last (new1.reverse ++ f1)）需要 n_list 幂循环机
  （Lebhirj/Hypermap.lemma_node_cycle/count_node_face/dart_of_card_node，
  全零命中）——归 E4/E5；
- E2 据此只落 split.2 支的**条件形**（三槽在案 ⇒ f_last split.2 成立），
  剩余义务形状由本定理钉死，E3 填槽即自动合流。 -/

/-- **AQ3-split2 条件形**（HOL AQ23.hl:311-:352 的 Lean 内核）：
三槽（y≠z、z∈face y、uniq split.2）在案 ⇒ `f_last L split.2`，即新环
r' = split.2 满足末元下一跳 = f_list（normal_list 合取 3 在 r' 处的
split.2 成员义务）。

证（对 HOL :311-:352 的逐步折算）：split.2 = ([z] ++ betwn r z y ++ [y])
++ betwn f y z（nextElPrevElUniq 环回 ram2' = z）。
- 空窗支（betwn f y z = []，HOL :311-:318）：getLast! = y，LHS
  nextEl split.2 y = head! split.2 = z（nextElLastHd，吃 hsnd）；RHS
  f_list L y = next_el f y = z（betwnNilNextOfNodup——exist_or_next_f
  空窗方向的纯列表内核，吃 hzface/hyne）。
- 非空窗支（HOL :344-:352）：getLast! = LAST window；LHS
  nextEl split.2 w = HD A = z（nextElAppendLastOfNodup = HOL
  next_el_cat_last2，吃 hsnd）；RHS f_list L w = next_el f w = z
  （find_face 相容 findFaceDarts_congr_of_mem + HOL next_last_betwn ✓
  JcajyduBetwnBase）。 -/
theorem aq3Split2FLast (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hyne : lYSpine L r x ≠ lZSpine L N r x)
    (hzface : lZSpine L N r x ∈ findFaceDarts L (lYSpine L r x))
    (hsnd : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2.Nodup) :
    fLastSpine L (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
  have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
  have hydart : lYSpine L r x ∈ listOfDarts L :=
    memYtransListOfDarts L hL hgn hm hf
  have hw : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hrnd _
  have hS2 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2
      = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (lZSpine L N r x) := by
    simp only [splitNormalListSpine]
    rw [hw]
  have hAne : ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ≠ [] := mem_imp_not_nil
    (List.mem_append.mpr (Or.inl (List.mem_cons_self ..)))
  have hyface : lYSpine L r x ∈ findFaceDarts L (lYSpine L r x) :=
    (dart_in_face L (lYSpine L r x)).mpr hydart
  by_cases hwne : between (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (lZSpine L N r x) = []
  · -- 空窗支（HOL :311-:318）
    have hsndA : ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]).Nodup := by
      have h1 : (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2
          = ([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
          ++ [lYSpine L r x]) ++ [] := by
        rw [hS2, hwne]
      rw [List.append_nil] at h1
      rw [← h1]
      exact hsnd
    have hbt : (between r (lZSpine L N r x) (lYSpine L r x)
        ++ [lYSpine L r x]) ≠ [] :=
      mem_imp_not_nil (List.mem_append.mpr (Or.inr (List.mem_cons_self ..)))
    have hAg : ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]).getLast hAne = lYSpine L r x :=
      (List.getLast_append_of_right_ne_nil [lZSpine L N r x]
        (between r (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x]) hbt).trans
      (List.getLast_append_of_right_ne_nil (between r (lZSpine L N r x)
        (lYSpine L r x)) [lYSpine L r x]
        (mem_imp_not_nil (List.mem_cons_self ..)))
    rw [hS2, hwne, List.append_nil]
    show nextEl ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) ([lZSpine L N r x] ++ between r
      (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x]).getLast!
      = fList L ([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]).getLast!
    have hl : nextEl ([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) (([lZSpine L N r x] ++ between r
        (lZSpine L N r x) (lYSpine L r x) ++ [lYSpine L r x]).getLast hAne)
        = lZSpine L N r x := by
      rw [nextElLastHd hsndA hAne]
      simp
    have hr : fList L (lYSpine L r x) = lZSpine L N r x := by
      show nextEl (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) = _
      exact betwnNilNextOfNodup (findFaceDarts_nodup hL.1 _) hyface hzface
        hyne hwne
    rw [getLast!EqGetLast hAne, hl, hAg, hr]
  · -- 非空窗支（HOL :344-:352）
    have hwne' : between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x) ≠ [] := hwne
    have hwmem : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).getLast hwne' ∈ between (findFaceDarts L
        (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) :=
      List.getLast_mem hwne'
    have hwface : (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).getLast hwne' ∈ findFaceDarts L (lYSpine L r x) :=
      memBetweenOfMem hwmem
    have hwd : findFaceDarts L ((between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x)).getLast hwne')
        = findFaceDarts L (lYSpine L r x) :=
      findFaceDarts_congr_of_mem hL.1 hydart hwface
    have hSne : (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++ between (findFaceDarts L
        (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)) ≠ [] :=
      mem_imp_not_nil (List.mem_append.mpr (Or.inr
        (List.getLast_mem hwne')))
    have hsnd' : (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++ between (findFaceDarts L
        (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).Nodup := by
      rw [← hS2]; exact hsnd
    have hwl : (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++ between (findFaceDarts L
        (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).getLast!
        = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).getLast hwne' := by
      rw [getLast!EqGetLast hSne,
        List.getLast_append_of_right_ne_nil _ _ hwne']
    have hl : nextEl (([lZSpine L N r x] ++ between r (lZSpine L N r x)
        (lYSpine L r x) ++ [lYSpine L r x]) ++ between (findFaceDarts L
        (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))
        ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).getLast hwne') = lZSpine L N r x := by
      rw [← getLast!EqGetLast hwne', nextElAppendLastOfNodup hsnd' hAne hwne']
      simp
    have hrhs : fList L ((between (findFaceDarts L (lYSpine L r x))
        (lYSpine L r x) (lZSpine L N r x)).getLast hwne')
        = lZSpine L N r x := by
      show nextEl (findFaceDarts L ((between (findFaceDarts L
        (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).getLast hwne'))
        ((between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x)).getLast hwne') = _
      rw [hwd]
      exact nextLastBetwn hyface hzface (findFaceDarts_nodup hL.1 _) hyne hwne'
    rw [hS2]
    show nextEl (([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) ++ between (findFaceDarts L
      (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x))
      (([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x)
      ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (lZSpine L N r x)).getLast!
      = fList L (([lZSpine L N r x] ++ between r (lZSpine L N r x)
      (lYSpine L r x) ++ [lYSpine L r x]) ++ between (findFaceDarts L
      (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).getLast!
    rw [hwl, hl, hrhs]

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 = 标准三 ⊆ [propext, Classical.choice,
Quot.sound]，零 sorryAx——本批五件零消费 TameList16:1109 在案债链。
落库时编排者可整体注释本节，不影响任何声明。） -/
#print axioms Kepler.Text.TameSpine.nextElAppendLastOfNodup
#print axioms Kepler.Text.TameSpine.memBetweenOfMem
#print axioms Kepler.Text.TameSpine.betwnNilNextOfNodup
#print axioms Kepler.Text.TameSpine.aq2
#print axioms Kepler.Text.TameSpine.aq3Split2FLast
