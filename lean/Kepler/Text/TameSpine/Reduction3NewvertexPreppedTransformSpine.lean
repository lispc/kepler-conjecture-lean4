/-
  Kepler.Text.TameSpine.Reduction3NewvertexPreppedTransformSpine — W2-件2 Wave C：
  `newvertex_prepped_transform`（reduction2.hl:1273-1345）的 spine 形主装。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ HOL `newvertex_prepped_transform`（reduction2.hl:1273-1345）：
  │ newvertex_prepped L N r x（+marked/¬final/r_trans_eq/元素区间）⇒
  │ newvertex_prepped L (ntrans … 1) (rtrans … 1) x。三段拼装：
  │ ① news 分裂（§1，face_diff_r 的 rest 识别精确形）：news@r = b ++ news@r'
  │   （b = MAP FST (filter (∉r) r') = face 新弧，rtransFilterEq）。分裂 =
  │   旋转分解 P ++ 新弧 ++ 尾段，滤子三段：P⊆r（leYInR）/ P⊆r'（B2e）
  │   新弧∉r（betwnNotInRtrans）/ 新弧⊆r'（rtransCat）/ 尾段 r↔r'（rRtransEqSpine）
  │ ② 计数（Wave A 引理）：n' = n + |b|；③ iota：news = range' n |news|（hnvp）
  │   ⇒ news' = drop |b| news = range' n' |news'|（drop_range' + 长度相消）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS ─────────────────────────────────────────────────────
  │ ① `rRtransEqSpine`（§0）＝ `Reduction5.rRtransEq`（Reduction5Base:249）的
  │    spine 镜像（lz↦lZSpine、rtrans↦rtransSpine）= HOL r_trans_eq_assumption
  │    的 spine 自洽形，本波**消费**（尾段等价）；链原形 hrre 留原文前提位透传。
  │ ② rotateTo 五私件按 b2d 先例同款重推导（HbridgeElim 私件跨文件不可取）。
  │ ③ 「z 前段 ⊆ r'」用 B2e ohcgkfuSpineV0 + indexfN 反位次，免位置簿记。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入；既有文件零触碰。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3NewvertexPrepTransform
import Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2e
import Kepler.Text.TameSpine.JcajyduTowerConsumers
import Kepler.Text.TameSpine.JcajyduAqSnd

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl dart_in_face findFaceDarts_nodup
  nextEl_mem_of_mem getElem_idxOf getD_eq_getElem_of_lt nextEl_eq_getD
  findFaceDarts_congr_of_mem elementsOfList)

variable {α : Type}

/-! ## §0 载体与私件重推导 -/

/-- **r_trans_eq_assumption 的 spine 自洽形**（Reduction5.rRtransEq 逐字段
镜像）：face 轨道 `indexf ≥ indexf w l'z` 的 dart 在 r 与 r' 间成员性不变。 -/
def rRtransEqSpine (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) : Prop :=
  let w := nextEl (findFaceDarts L x) x
  ∀ x' ∈ findFaceDarts L x,
    indexf w (lZSpine L N r x) (findFaceDarts L x) ≤ indexf w x' (findFaceDarts L x) →
      (x' ∈ r ↔ x' ∈ rtransSpine L N r x 1)

/-- splitAt 版 `rotateTo` 的 List.rotate 形（同款重推导）。 -/
private theorem rotateTo_eq_rotateW {α : Type} [BEq α] [LawfulBEq α] {f : List α} {v : α}
    (hv : v ∈ f) :
    Kepler.Text.Reduction3.rotateTo f v = f.rotate (f.idxOf v) := by
  have hlt : f.idxOf v < f.length := List.idxOf_lt_length_iff.mpr hv
  simp only [Kepler.Text.Reduction3.rotateTo, Kepler.Graphs.splitAt]
  rw [sndSplitAtDrop f v [], fstSplitAtTake f v [], List.nil_append,
    List.rotate_eq_drop_append_take (n := f.idxOf v) (Nat.le_of_lt hlt),
    List.drop_eq_getElem_cons hlt, List.getElem_idxOf hlt]

/-- `nextEl` 的下标形（同款重推导）。 -/
private theorem nextElIdxOfW [BEq α] [LawfulBEq α] [DecidableEq α] {f : List α} {x : α}
    (hnd : f.Nodup) (hx : x ∈ f) :
    f.idxOf (Kepler.Assembly.nextEl f x) = (f.idxOf x + 1) % f.length := by
  have hlt : f.idxOf x < f.length := List.idxOf_lt_length_iff.mpr hx
  have hpos : 0 < f.length := List.length_pos_of_mem hx
  rw [Kepler.Assembly.nextEl]
  by_cases hlast : f.idxOf x = f.length - 1
  · rw [if_pos hlast]
    have hhead : f.headD x = f[0]'hpos := by
      cases f with
      | nil => exact absurd hx (List.not_mem_nil)
      | cons a t => rfl
    rw [hhead]
    have h0 : f.idxOf (f[0]'hpos) = 0 := by
      have h := hnd.idxOf_getElem 0 hpos
      simpa using h
    rw [h0]
    rw [show (f.idxOf x + 1) % f.length = 0 from by
      rw [hlast, show f.length - 1 + 1 = f.length from by omega, Nat.mod_self]]
  · rw [if_neg hlast]
    have hnext : f.idxOf x + 1 < f.length := by omega
    rw [getD_eq_getElem_of_lt hnext, hnd.idxOf_getElem (f.idxOf x + 1) hnext,
      Nat.mod_eq_of_lt hnext]

/-- 旋转一步的滤子不变（同款重推导）：被旋出的首元 ∈ r 时滤子不变。 -/
private theorem filterRotateStepW [BEq α] [LawfulBEq α] [DecidableEq α] {f : List α}
    (hnd : f.Nodup) {x : α} (hx : x ∈ f) (r : List α) (hxr : x ∈ r) :
    (f.rotate (f.idxOf x)).filter (fun d => decide (d ∉ r))
      = (f.rotate (f.idxOf x + 1)).filter (fun d => decide (d ∉ r)) := by
  have hlt : f.idxOf x < f.length := List.idxOf_lt_length_iff.mpr hx
  have htake : f.take (f.idxOf x + 1) = f.take (f.idxOf x) ++ [x] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlt]
    simp only [Option.toList_some]
    rw [List.getElem_idxOf hlt]
  rw [List.rotate_eq_drop_append_take (n := f.idxOf x) (Nat.le_of_lt hlt),
    List.rotate_eq_drop_append_take (n := f.idxOf x + 1) (Nat.succ_le_of_lt hlt),
    List.drop_eq_getElem_cons hlt, List.getElem_idxOf hlt, htake,
    List.cons_append, List.filter_append,
    List.filter_cons_of_neg (by simp [hxr]),
    List.filter_append, List.filter_append]
  have hx' : (List.filter (fun d => decide (d ∉ r)) [x]) = [] := by simp [hxr]
  rw [hx', List.append_nil]

/-- **newvertex_alt 核心**（同款重推导）：x 旋转与 w = nextEl f x 旋转在
双重点成员滤除后相等。 -/
private theorem rotateToFilterSwapW {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {f : List α} {x : α} (hnd : f.Nodup) (hx : x ∈ f) {r : List α} (hxr : x ∈ r)
    (hwr : Kepler.Assembly.nextEl f x ∈ r) :
    (Kepler.Text.Reduction3.rotateTo f x).filter (fun d => decide (d ∉ r))
      = (Kepler.Text.Reduction3.rotateTo f (Kepler.Assembly.nextEl f x)).filter
        (fun d => decide (d ∉ r)) := by
  have hw : Kepler.Assembly.nextEl f x ∈ f := nextEl_mem_of_mem hx
  rw [rotateTo_eq_rotateW hx, rotateTo_eq_rotateW hw, nextElIdxOfW hnd hx,
    List.rotate_mod]
  exact filterRotateStepW hnd hx r hxr

/-- 旋转点下标 ↔ `indexf`（同款重推导）。 -/
private theorem idxOfRotateEqIndexfW [BEq α] [LawfulBEq α] [DecidableEq α]
    {f : List α} (hnd : f.Nodup) (hpos : 0 < f.length) {w z : α} (hw : w ∈ f)
    (hz : z ∈ f) :
    (f.rotate (f.idxOf w)).idxOf z = indexf w z f := by
  have hilt : f.idxOf w < f.length := List.idxOf_lt_length_iff.mpr hw
  have hk : (f.rotate (f.idxOf w)).idxOf z < f.length :=
    Nat.lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr (List.mem_rotate.mpr hz))
      (List.length_rotate f (f.idxOf w)).le
  have hxk : (f.rotate (f.idxOf w))[(f.rotate (f.idxOf w)).idxOf z]'
      (List.idxOf_lt_length_iff.mpr (List.mem_rotate.mpr hz)) = z :=
    getElem_idxOf (List.mem_rotate.mpr hz)
  have hndr : (f.rotate (f.idxOf w)).Nodup := List.nodup_rotate.mpr hnd
  have hstep : (f.rotate (f.idxOf w))[(f.rotate (f.idxOf w)).idxOf z]'
      (List.idxOf_lt_length_iff.mpr (List.mem_rotate.mpr hz))
      = f[((f.rotate (f.idxOf w)).idxOf z + f.idxOf w) % f.length]'
        (Nat.mod_lt _ hpos) :=
    List.getElem_rotate f (f.idxOf w) _ (List.idxOf_lt_length_iff.mpr (List.mem_rotate.mpr hz))
  have hfidx : f.idxOf z = ((f.rotate (f.idxOf w)).idxOf z + f.idxOf w) % f.length := by
    conv_lhs => rw [← hxk, hstep]
    rw [hnd.idxOf_getElem (((f.rotate (f.idxOf w)).idxOf z + f.idxOf w) % f.length)
      (Nat.mod_lt _ hpos)]
  rw [indexf, if_pos ⟨hw, hz⟩, hfidx]
  rcases Nat.lt_or_ge ((f.rotate (f.idxOf w)).idxOf z + f.idxOf w) f.length
    with hc | hc
  · rw [Nat.mod_eq_of_lt hc, show (f.rotate (f.idxOf w)).idxOf z + f.idxOf w
      + (f.length - f.idxOf w) = (f.rotate (f.idxOf w)).idxOf z + f.length
      from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  · rw [Nat.mod_eq_sub_mod hc,
      Nat.mod_eq_of_lt (show (f.rotate (f.idxOf w)).idxOf z + f.idxOf w
        - f.length < f.length from by omega),
      show (f.rotate (f.idxOf w)).idxOf z + f.idxOf w - f.length
        + (f.length - f.idxOf w) = (f.rotate (f.idxOf w)).idxOf z
        from by omega, Nat.mod_eq_of_lt hk]

/-! ## §1 news 分裂（face_diff_r 的 rest 识别精确形） -/

/-- **news 分裂等式**：`news@r = b ++ news@r'`（b = MAP FST (filter (∉r) r')）；
滤子三段见文件头 ①，尾段等价 = `rRtransEqSpine`。 -/
theorem newsFilterSplitSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hrreS : rRtransEqSpine L N r x) :
    Kepler.Text.Reduction3.newvertex L r x
      = ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map (fun d => d.1)
        ++ Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hrnd : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hwr : nextEl (findFaceDarts L x) x ∈ r := aq10_nextMarkMemRTrans L hL hgn hm
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x := nextEl_mem_of_mem hxx
  have hndf : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hpos : 0 < (findFaceDarts L x).length := List.length_pos_of_mem hxx
  obtain ⟨hyf, hzf⟩ := markedLemmaYzInFace L hL hgn hunL hm hf
  have hyne : lYSpine L r x ≠ lZSpine L N r x := hqymrtx3List L hL hgn hunL hm hf
  -- r' 侧两点：x ∈ r'（状态 1 marked）与 w ∈ r'（aqs_nextMarkCaseMem 两案）
  have hm1 : MarkedListSpineFull hL (ntransSpine L N r x 1) (rtransSpine L N r x 1) x :=
    aqiunpp3_top L hL 1 hgn hm
  have hxr' : x ∈ rtransSpine L N r x 1 := hm1.1.2.2.2.1
  have hwr' : nextEl (findFaceDarts L x) x ∈ rtransSpine L N r x 1 := by
    have hcase := aqs_nextMarkCaseMem L hL hgn (N := N) (r := r) (x := x) hm hf
      (f := findFaceDarts L x) (w := nextEl (findFaceDarts L x) x) rfl rfl
    rcases hcase with h | h
    · rw [h, rtransCat L N r x hf hrnd]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    · rw [rtransCat L N r x hf hrnd]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
  -- 旋转坐标 G 与其段分解
  set G := (findFaceDarts L x).rotate
    ((findFaceDarts L x).idxOf (nextEl (findFaceDarts L x) x)) with hG
  have hndG : G.Nodup := by rw [hG]; exact List.nodup_rotate.mpr hndf
  have hyG : lYSpine L r x ∈ G := by rw [hG]; exact List.mem_rotate.mpr hyf
  have hzG : lZSpine L N r x ∈ G := by rw [hG]; exact List.mem_rotate.mpr hzf
  have hiy : G.idxOf (lYSpine L r x) = indexf (nextEl (findFaceDarts L x) x)
      (lYSpine L r x) (findFaceDarts L x) := by
    rw [hG]
    exact idxOfRotateEqIndexfW hndf hpos hwf hyf
  have hiz : G.idxOf (lZSpine L N r x) = indexf (nextEl (findFaceDarts L x) x)
      (lZSpine L N r x) (findFaceDarts L x) := by
    rw [hG]
    exact idxOfRotateEqIndexfW hndf hpos hwf hzf
  have hpG : G.idxOf (lYSpine L r x) = lMSpine L r x :=
    hiy.trans (indexfYtransEqLm L hL hgn hunL hm hf)
  have hpq : G.idxOf (lYSpine L r x) < G.idxOf (lZSpine L N r x) := by
    rw [hiy, hiz]
    exact pplhulj3V0 L hL hgn hunL hm hf
  have hbetw' : between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)
      = between G (lYSpine L r x) (lZSpine L N r x) := by
    rw [hG]
    exact betwnRot hndf hyf hzf hyne _
  have hsplitG : G = G.take (G.idxOf (lYSpine L r x) + 1)
      ++ G.drop (G.idxOf (lYSpine L r x) + 1) := (List.take_append_drop _ G).symm
  have hdrop : G.drop (G.idxOf (lYSpine L r x) + 1)
      = (G.drop (G.idxOf (lYSpine L r x) + 1)).take
          (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1))
        ++ (G.drop (G.idxOf (lYSpine L r x) + 1)).drop
            (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1)) :=
    (List.take_append_drop _ _).symm
  have hbtd : between G (lYSpine L r x) (lZSpine L N r x)
      = (G.drop (G.idxOf (lYSpine L r x) + 1)).take
          (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1)) := by
    rw [betwnTakeDrop hndG hzG, if_pos hpq]
  -- (a) 前缀 ⊆ r（leYInR）
  have hPf : ∀ d ∈ G.take (G.idxOf (lYSpine L r x) + 1), d ∈ r := by
    intro d hd
    obtain ⟨j, hj, hjd⟩ := List.mem_take_iff_getElem.mp hd
    have hjG : j < G.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have hdf : d ∈ findFaceDarts L x := by
      rw [hG] at hd
      exact List.mem_rotate.mp (List.mem_of_mem_take hd)
    have hidx : G.idxOf d = j := by
      have h := hndG.idxOf_getElem j hjG
      rwa [hjd] at h
    have hjle : j ≤ lMSpine L r x := by
      have h1 : j < G.idxOf (lYSpine L r x) + 1 := lt_of_lt_of_le hj (Nat.min_le_left _ _)
      rw [hpG] at h1
      omega
    refine leYInR L hL hgn hunL hm hf hdf ?_
    have hix : indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x) = G.idxOf d := by
      rw [hG]
      exact (idxOfRotateEqIndexfW hndf hpos hwf hdf).symm
    exact le_of_eq_of_le (hix.trans hidx) hjle
  -- (b) 前缀 ⊆ r'（B2e 成员性 + indexfN 反位次）
  have hPr' : ∀ d ∈ G.take (G.idxOf (lYSpine L r x) + 1),
      d ∈ rtransSpine L N r x 1 := by
    intro d hd
    obtain ⟨j, hj, hjd⟩ := List.mem_take_iff_getElem.mp hd
    have hjG : j < G.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have hdf : d ∈ findFaceDarts L x := by
      rw [hG] at hd
      exact List.mem_rotate.mp (List.mem_of_mem_take hd)
    have hidx : G.idxOf d = j := by
      have h := hndG.idxOf_getElem j hjG
      rwa [hjd] at h
    have hix : indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x) = G.idxOf d := by
      rw [hG]
      exact (idxOfRotateEqIndexfW hndf hpos hwf hdf).symm
    have hjle : G.idxOf d ≤ G.idxOf (lZSpine L N r x) := by
      have h1 : j < G.idxOf (lYSpine L r x) + 1 := lt_of_lt_of_le hj (Nat.min_le_left _ _)
      omega
    have hdEq : d = (nextEl (findFaceDarts L x))^[indexf (nextEl (findFaceDarts L x) x) d
        (findFaceDarts L x)] (nextEl (findFaceDarts L x) x) :=
      (indexfN hwf hdf hndf).symm
    rw [hdEq]
    refine ohcgkfuSpineV0 L hL hgn hm hf rfl rfl ?_
    rw [hix, ← hiz]
    exact hjle
  -- (c) 新弧 ∉ r（betwnNotInRtrans）
  have hcomp : ∀ d ∈ between G (lYSpine L r x) (lZSpine L N r x), d ∉ r := by
    intro d hd
    have hd' : d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) := by
      have h := hd
      rw [← hbetw'] at h
      exact h
    refine betwnNotInRtrans L hL hgn hunL hm hf ?_
    rw [findFaceDarts_congr_of_mem hL.1 hxd hyf]
    exact hd'
  -- (d) 新弧 ⊆ r'（rtransCat 的 face 段）
  have hbFr' : ∀ d ∈ between G (lYSpine L r x) (lZSpine L N r x),
      d ∈ rtransSpine L N r x 1 := by
    intro d hd
    have hd' : d ∈ between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) := by
      have h := hd
      rw [← hbetw'] at h
      exact h
    have hd'' : d ∈ between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x)
        (lZSpine L N r x) := by
      rwa [findFaceDarts_congr_of_mem hL.1 hxd hyf]
    rw [rtransCat L N r x hf hrnd]
    exact List.mem_append_right _ hd''
  -- (e) 尾段 ∈ r ↔ ∈ r'（rRtransEqSpine）
  have hTr : ∀ d ∈ (G.drop (G.idxOf (lYSpine L r x) + 1)).drop
      (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1)),
      (d ∈ r ↔ d ∈ rtransSpine L N r x 1) := by
    intro d hd
    have hdG : d ∈ G.drop (G.idxOf (lZSpine L N r x)) := by
      have h := hd
      rw [List.drop_drop] at h
      rwa [show G.idxOf (lYSpine L r x) + 1 + (G.idxOf (lZSpine L N r x)
        - (G.idxOf (lYSpine L r x) + 1)) = G.idxOf (lZSpine L N r x) from by omega] at h
    have hdG' : d ∈ G := List.mem_of_mem_drop hdG
    have hdf : d ∈ findFaceDarts L x := by
      rw [hG] at hdG'
      exact List.mem_rotate.mp hdG'
    have hix : indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x) = G.idxOf d := by
      rw [hG]
      exact (idxOfRotateEqIndexfW hndf hpos hwf hdf).symm
    have hge : G.idxOf (lZSpine L N r x) ≤ G.idxOf d :=
      (memDropIndex hndG hdG').mp hdG
    exact hrreS d hdf (by rw [← hiz, hix]; exact hge)
  -- 滤子代数
  have hPfNil : List.filter (fun d => decide (d ∉ r))
      (G.take (G.idxOf (lYSpine L r x) + 1)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd
    simp [hPf d hd]
  have hKeepSelf : List.filter (fun d => decide (d ∉ r))
      (between G (lYSpine L r x) (lZSpine L N r x))
      = between G (lYSpine L r x) (lZSpine L N r x) := by
    rw [List.filter_eq_self]
    intro d hd
    simp [hcomp d hd]
  have hfiltT : List.filter (fun d => decide (d ∉ r))
      ((G.drop (G.idxOf (lYSpine L r x) + 1)).drop
        (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1)))
      = List.filter (fun d => decide (d ∉ rtransSpine L N r x 1))
        ((G.drop (G.idxOf (lYSpine L r x) + 1)).drop
          (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1))) := by
    apply List.filter_congr
    intro d hd
    exact decide_eq_decide.mpr (not_congr (hTr d hd))
  have hPrNil : List.filter (fun d => decide (d ∉ rtransSpine L N r x 1))
      (G.take (G.idxOf (lYSpine L r x) + 1)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd
    simp [hPr' d hd]
  have hbFNil : List.filter (fun d => decide (d ∉ rtransSpine L N r x 1))
      (between G (lYSpine L r x) (lZSpine L N r x)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd
    simp [hbFr' d hd]
  have hfilt' : List.filter (fun d => decide (d ∉ rtransSpine L N r x 1)) G
      = List.filter (fun d => decide (d ∉ rtransSpine L N r x 1))
        ((G.drop (G.idxOf (lYSpine L r x) + 1)).drop
          (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1))) := by
    conv_lhs => rw [hsplitG, hdrop]
    rw [List.filter_append, List.filter_append, ← hbtd, hPrNil, hbFNil,
      List.nil_append, List.nil_append]
  have hfilt : List.filter (fun d => decide (d ∉ r)) G
      = between G (lYSpine L r x) (lZSpine L N r x)
        ++ List.filter (fun d => decide (d ∉ rtransSpine L N r x 1)) G := by
    conv_lhs => rw [hsplitG, hdrop]
    rw [List.filter_append, List.filter_append, ← hbtd, hPfNil, hKeepSelf, hfiltT,
      List.nil_append, hfilt']
  -- 组装：dart 等式 → map 等式
  rw [show Kepler.Text.Reduction3.newvertex L r x
      = ((Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) x).filter
          (fun d => decide (d ∉ r))).map (fun d => d.1) from rfl,
    show Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x
      = ((Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) x).filter
          (fun d => decide (d ∉ rtransSpine L N r x 1))).map (fun d => d.1) from rfl,
    rtransFilterEq L hL hgn hunL hm hf, ← List.map_append]
  congr 1
  rw [rotateToFilterSwapW hndf hxx hxr hwr,
    rotateToFilterSwapW hndf hxx hxr' hwr',
    rotateTo_eq_rotateW hwf, ← hG,
    findFaceDarts_congr_of_mem hL.1 hxd hyf, hbetw']
  exact hfilt

/-! ## §2 主件：newvertex_prepped_transform 的 spine 形 -/

/-- **HOL `newvertex_prepped_transform`**（reduction2.hl:1273-1345）spine 形。 -/
theorem newvertexPreppedTransformSpine (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hrre : Kepler.Text.Reduction5.rRtransEq L N r x)
    (hm : MarkedListSpineFull hL N r x)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hf : ¬finalListSpine L r)
    (hold : elementsOfList (Kepler.Text.Reduction5.quotientList L N)
      = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1})
    (hrreS : rRtransEqSpine L N r x) :
    Kepler.Text.Reduction3.newvertexPrepped L (ntransSpine L N r x 1)
      (rtransSpine L N r x 1) x := by
  have hA := newvertexPreppedTransformLemmaSpine L hL hgn hrre hm hnvp hf hold
  have hnewSplit := newsFilterSplitSpine L hL hgn hm hf hrreS
  -- news = range' n |news|（状态 0 非 final 支）
  have hnews : Kepler.Text.Reduction3.newvertex L r x
      = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
          (Kepler.Text.Reduction3.newvertex L r x).length := by
    have h := hnvp
    rw [show Kepler.Text.Reduction3.newvertexPrepped L N r x =
        (finalListSpine L r ∨ Kepler.Text.Reduction3.newvertex L r x
          = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
              (Kepler.Text.Reduction3.newvertex L r x).length) from rfl] at h
    rcases h with hfin | h
    · exact absurd hfin hf
    · exact h
  have hlen : (Kepler.Text.Reduction3.newvertex L r x).length
      = (((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1)).length
        + (Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x).length := by
    rw [hnewSplit, List.length_append]
  have hnews' : Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x
      = List.range' (((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length)
          (Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x).length := by
    have hdrop : Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x
        = List.range' ((N.flatten.map (fun d => d.1)).dedup.length
            + (((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
              (fun d => d.1)).length)
            ((Kepler.Text.Reduction3.newvertex L r x).length
              - (((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
                (fun d => d.1)).length) := by
      conv_lhs =>
        rw [show Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x
            = (Kepler.Text.Reduction3.newvertex L r x).drop
                (((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
                  (fun d => d.1)).length from by rw [hnewSplit, List.drop_left],
          hnews, List.drop_range']
      simp only [Nat.mul_one]
    conv_lhs => rw [hdrop]
    have hidx : (N.flatten.map (fun d => d.1)).dedup.length
        + (((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)).length
        = ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length := hA.symm
    have hlen' : (Kepler.Text.Reduction3.newvertex L r x).length
        - (((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)).length
        = (Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x).length := by
      omega
    rw [hidx, hlen']
  rw [show Kepler.Text.Reduction3.newvertexPrepped L (ntransSpine L N r x 1)
      (rtransSpine L N r x 1) x =
      (finalListSpine L (rtransSpine L N r x 1) ∨
        Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x
          = List.range' (((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length)
              (Kepler.Text.Reduction3.newvertex L (rtransSpine L N r x 1) x).length) from rfl]
  exact Or.inr hnews'

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.rRtransEqSpine
#print axioms Kepler.Text.TameSpine.newsFilterSplitSpine
#print axioms Kepler.Text.TameSpine.newvertexPreppedTransformSpine
