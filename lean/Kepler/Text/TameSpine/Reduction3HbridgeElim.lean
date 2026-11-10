/-
  Kepler.Text.TameSpine.Reduction3HbridgeElim — W2-件1a：`hbridge` 槽闭合
  （`elements_of_list_ntrans` 的无条件形，HOL reduction2.hl:1042-1136 全量）。

  ┌─ 状态（2026-11-10 续跑完成）───────────────────────────────────
  │ §0 泛型旋转/轨道工具层 8 件（7936ba22 已落库）+ §1 主装
  │ `elementsOfListNtransTop` 无条件形（本 patch 新增）：§1 工具层 5 件
  │ （rotateTo_eq_rotate/rotateToGetD/nextElIdxOf/filterRotateStep/
  │ rotateToFilterSwap）+ §2 桥件 2 件（rtransFilterEq/leYInR：HOL
  │ rtrans_diff_r:489 与 le_y_in_r:690 的结论级形）+ §3 分解与数算
  │ （newsSplit 三段分解 / take_range'_eq / setOfListNatSpine_range'）
  │ + §4 主定理（case B apply 件1 `elementsOfListNtrans` 全量、LEBHIRJ
  │ 零重证；case A v = [] 走 LEBHIRJ 组装段同款重推导 + 计数相等）。
  │ 岛编 RC=0 零 error 零 warning；探针 elementsOfListNtransTop 与
  │ newsSplit/leYInR = [propext, Classical.choice, Quot.sound]，零
  │ 未证占位/变体求值（compile_1a2_probe.log）。NCVIBWU2/3（Ncvibwu.hl
  │ :425/:1132，~1000 行）按免移植判定未被消费（rest 不识别；face_diff_r
  │ 的 cat_eq 两侧精确对齐同免）。
  └────────────────────────────────────────────────────────────────

  ┌─ 与已落库件1（011c0451，Reduction3ElementsOfListNtrans）的关系 ─
  │ 件1 主定理携带显式前提 `hbridge`（HOL 1085-1089 ENOUGH_TO_SHOW 内
  │ 切口：∃k, n ≤ k ∧ set(MAP FST (filter (¬MEM r) r')) = n..k，
  │ n = fn.dedup.length、r' = rtrans L N r x 1）。本件目标：由
  │ `newvertexPrepped`（news = List.range' n …）闭合它，得无条件形。
  │ §1 路线图（侦察定型，已按此完成，各条即落点）：
  │ ① case A（v = []，HOL 1075 + 1128-1136 反证支）：件1 的 LEBHIRJ
  │   组装段（sCase/fCase/hsub/hsup/hsupv/hpoint，件1 :193-327）原样
  │   照搬，hvIff 换成「i ∈ v ↔ False」，htofin/hK 的 omega 直接收口
  │   ——零新料。
  │ ② case B（v ≠ []）：HOL 同路 = news 前缀分解 + take 数算 +
  │   hbridge := ⟨n+l-1, _, _⟩ ⇒ `exact elementsOfListNtrans`（件1
  │   全量）。前缀分解 `news = MAP FST (filter (∉r) r') ++ rest` 三件：
  │   a. **rtrans_diff_r 树内组装**（HOL :489 结论级）：
  │      filter(∉r) r' = betwn f y z —— `rtransCat`（JcajyduRed2Trans
  │      :171）+ `List.filter_append` + z,y ∈ r 消端点（件1 :181-182
  │      的 ytransMemRtrans/zMemRtransClean）+ `betwnMem` 消 between r
  │      z y + `betwnNotInRtrans`（JcajyduAqSnd:136，face 弧 ∉ r）+
  │      `findFaceDarts_congr_of_mem`（f_y = f_x 桥，喂 marked_lemma_
  │      yz_in_face TameList18:96 的 y ∈ face）≈ 40 行。
  │   b. **le_y_in_r 轨道化**（HOL :690-780）：fw 上 [0, idx y] ⊆ r
  │      （含 w = nextEl f x ∈ r 的 i=w 情形）——原料全在树：
  │      `lYRepPowerLe`（JcajyduAqLeaf10:246）+ `fListPowEqNextElPow`
  │      + `indexfYtransEqLm`（JcajyduAqZIndexf:109/136）+ §0
  │      `idxOfRotateEqIndexf`（indexl↔orbit 下标换算桥）≈ 50 行。
  │   c. **NCVIBWU 免移植（本轮精确化判定）**：face_diff_r 的 rest 半件
  │      （filter(∉r') fw）与 NCVIBWU2/3（Ncvibwu.hl:425/1132，~1000 行
  │      幂轨道下标精确性主山，树内零命中）在弱化形下不被消费——rest
  │      只进 `++ rest` 尾巴不识别。HOL 的 cat_eq 两侧精确对齐（含
  │      indexl_y_lt_z/betwn_rotate_to_face）同免。
  │   d. **news 段分解**：`(rotateTo f x).filter(∉r)` 按 orbit 下标切三段
  │      （[0,idx y] ∈ r 被杀 / (idx y,idx z] = betwn f y z ∉ r 全保 /
  │      (idx z,len] = rest 不识别）——表级实现 ≈ 60 行，§0 getD 工具
  │      直配（rotateTo-orbit 表等式 ≈ 30 行待落：(rotateTo f v)[j] =
  │      f.getD ((f.idxOf v + j) % f.length) v）。
  │   e. **take 数算**（HOL 1117-1136）：news = range' n (len news)
  │      （hnvp 展开）⇒ take l news = range' n l ⇒ set = {n..n+l-1}，
  │      l ≥ 1（case B）⇒ k := n+l-1 ≈ 20 行（core/Mathlib 级零缺口）。
  │ ③ 行数账：§0 已 195 行 + §1（a,b,d,e + 件1 组装段照搬 ~90 + case
  │   收口 ~25）≈ 500 > 450。§0 是既需基建（b/c/d 全消费），先交。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（公理/未证占位/变体求值均无）；主仓零写入（untracked 亦禁，
  │ 本件全程 /tmp 编译：cd 主仓 lean 导 LEAN_PATH 后 cd 车道 lean 跑裸
  │ lean，containment 按 cwd 判定）。既有文件零触碰（w22 系先例：另立
  │ 无条件形）。rotateTo = 链岛 Kepler.Text.Reduction3.rotateTo（splitAt
  │ post-排除首元，ListAux.lean:18 同源）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3ElementsOfListNtrans
import Kepler.Text.TameSpine.TameList35
import Kepler.Text.TameSpine.TameList5
import Kepler.Text.TameSpine.TameList72
import Kepler.Text.TameSpine.JcajyduBetwnRot
import Kepler.Text.TameSpine.TameList18
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.TameSpine.JcajyduAqLeaf10
import Kepler.Text.TameSpine.JcajyduAqSnd
import Kepler.Text.TameSpine.JcajyduAqLeaf1B
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.TameSpine.JcajyduAqZIndexf
import Kepler.Text.TameSpine.JcajyduAqZUnlock
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsNewVertex
import Kepler.Text.Reduction5Base

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between splitAt)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (elementsOfList GoodListNodesTl nextEl_mem_of_mem
  prevEl_mem_of_mem hypermapOfList dart_in_face findFaceDarts_congr_of_mem
  mem_darts_of_mem_findFace nextEl_eq_getD getD_eq_getElem_of_lt
  dart_in_face findFaceDarts_nodup findFaceDarts_congr_of_mem)

variable {α : Type*}

/-! ## §0 泛型旋转/轨道工具（rotateTo = 链岛 Kepler.Text.Reduction3.rotateTo，
splitAt post-排除首元，ListAux.lean:18 / ListAux.thy:550 同源；getElem 位证雷区
全部以 getD/显式 'h 形规避） -/

/-- nextEl 幂保成员（ZIndexf 私件同证重推导，避免跨文件私依赖）。 -/
private theorem orbitMem [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    {x : α} (hx : x ∈ s) : ∀ k : ℕ, (nextEl s)^[k] x ∈ s := by
  intro k
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact nextEl_mem_of_mem ih

/-- 成员 ⇒ 下标界。 -/
private theorem idxOfLt [BEq α] [LawfulBEq α] {s : List α} {a : α} (h : a ∈ s) :
    s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr h

/-- 下标取元：`s[s.idxOf a] = a`。 -/
private theorem getElemIdxOf [BEq α] [LawfulBEq α] {s : List α} {a : α} (h : a ∈ s) :
    s[s.idxOf a]'(List.idxOf_lt_length_iff.mpr h) = a := by
  induction s with
  | nil => exact absurd h (List.not_mem_nil (a := a))
  | cons b t ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    · by_cases hbv : (b == a) = true
      · have hb : b = a := by simp at hbv; exact hbv
        simp [hb, List.idxOf_cons_self]
      · have hne : b ≠ a := by simp at hbv; exact fun hc => hbv hc
        simp only [List.idxOf_cons_ne t hne, List.getElem_cons_succ]
        exact ih hm

/-- getD 下标取元：`f.getD (f.idxOf a) a = a`。 -/
private theorem getDIdxOfSelf [BEq α] [LawfulBEq α] {f : List α} {a : α} (h : a ∈ f) :
    f.getD (f.idxOf a) a = a := by
  induction f with
  | nil => rfl
  | cons b t ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    · by_cases hbv : (b == a) = true
      · have hb : b = a := by simp at hbv; exact hbv
        simp [hb, List.idxOf_cons_self]
      · have hne : b ≠ a := by simp at hbv; exact fun hc => hbv hc
        rw [List.idxOf_cons_ne t hne, List.getD_cons_succ]
        exact ih hm

/-- getD 下标单射：界内 getD 的 idxOf 复原下标。 -/
private theorem getDIdxEq [BEq α] [LawfulBEq α] [DecidableEq α] {f : List α}
    (hnd : f.Nodup) (hpos : 0 < f.length) (m : ℕ) (d : α) :
    f.idxOf (f.getD (m % f.length) d) = m % f.length := by
  rw [getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  exact hnd.idxOf_getElem (m % f.length) (Nat.mod_lt _ hpos)

/-- `(m % len + 1) % len = (m + 1) % len`（ZIndexf modSuccMod 同证：
div_add_mod + add_mul_mod_self_left，规避 mod-变元 omega 盲区）。 -/
private theorem modSuccEq (m len : ℕ) : (m % len + 1) % len = (m + 1) % len := by
  have h : m + 1 = len * (m / len) + (m % len + 1) := by
    have := Nat.div_add_mod m len
    omega
  rw [h, Nat.add_comm (len * (m / len)), Nat.add_mul_mod_self_left]

/-- **轨道枚举（getD 形）**：w 起 orbit j 步 = 线性表 (idx w + j) mod len 处。 -/
private theorem orbitEnumGetD [BEq α] [LawfulBEq α] [DecidableEq α] {f : List α}
    (hnd : f.Nodup) (hpos : 0 < f.length) {w : α} (hw : w ∈ f) (j : ℕ) :
    (nextEl f)^[j] w = f.getD ((f.idxOf w + j) % f.length) w := by
  have hilt : f.idxOf w < f.length := List.idxOf_lt_length_iff.mpr hw
  induction j with
  | zero => rw [Function.iterate_zero_apply, Nat.add_zero, Nat.mod_eq_of_lt hilt,
      getDIdxOfSelf hw]
  | succ k ih =>
    have hmk : (f.idxOf w + k) % f.length < f.length := Nat.mod_lt _ hpos
    have hm : f.getD ((f.idxOf w + k) % f.length) w ∈ f := by
      rw [getD_eq_getElem_of_lt hmk]
      exact List.getElem_mem hmk
    rw [Function.iterate_succ_apply', ih, nextEl_eq_getD hm,
      getDIdxEq hnd hpos _ w, modSuccEq, Nat.add_assoc,
      getD_eq_getElem_of_lt (hj := Nat.mod_lt (f.idxOf w + (k + 1)) hpos)
        (d := w),
      getD_eq_getElem_of_lt hmk,
      getD_eq_getElem_of_lt
        (hj := Nat.mod_lt (f.idxOf w + (k + 1)) hpos)]

/-- **rotate 表下标 = indexf**（getElem_rotate + Nodup 下标单射 + indexf 展开；
P4/P6 共用桥）。 -/
private theorem idxOfRotateEqIndexf [BEq α] [LawfulBEq α] [DecidableEq α]
    {f : List α} (hnd : f.Nodup) (hpos : 0 < f.length) {w z : α} (hw : w ∈ f)
    (hz : z ∈ f) :
    (f.rotate (f.idxOf w)).idxOf z = indexf w z f := by
  have hilt : f.idxOf w < f.length := idxOfLt hw
  have hk : (f.rotate (f.idxOf w)).idxOf z < f.length :=
    Nat.lt_of_lt_of_le (idxOfLt (List.mem_rotate.mpr hz))
      (List.length_rotate f (f.idxOf w)).le
  have hxk : (f.rotate (f.idxOf w))[(f.rotate (f.idxOf w)).idxOf z]'
      (List.idxOf_lt_length_iff.mpr (List.mem_rotate.mpr hz)) = z :=
    getElemIdxOf (h := List.mem_rotate.mpr hz)
  have hndr : (f.rotate (f.idxOf w)).Nodup := List.nodup_rotate.mpr hnd
  have hstep : (f.rotate (f.idxOf w))[(f.rotate (f.idxOf w)).idxOf z]'
      (List.idxOf_lt_length_iff.mpr (List.mem_rotate.mpr hz))
      = f[((f.rotate (f.idxOf w)).idxOf z + f.idxOf w) % f.length]'
        (Nat.mod_lt _ hpos) :=
    List.getElem_rotate f (f.idxOf w) _ (idxOfLt (List.mem_rotate.mpr hz))
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
/-! ## §1 主装工具层（W2-件1a §1：HOL 1042-1136 的桥件；路线图 §3a-e） -/

/-- splitAt 版 rotateTo 的 List.rotate 形（v ∈ f；§0 getD 工具与 Mathlib rotate
件的桥）：`rotateTo f v = f.rotate (f.idxOf v)`。 -/
private theorem rotateTo_eq_rotate {α : Type} [BEq α] [LawfulBEq α] {f : List α} {v : α}
    (hv : v ∈ f) :
    Kepler.Text.Reduction3.rotateTo f v = f.rotate (f.idxOf v) := by
  have hlt := idxOfLt hv
  simp only [Kepler.Text.Reduction3.rotateTo, Kepler.Graphs.splitAt]
  rw [sndSplitAtDrop f v [], fstSplitAtTake f v [], List.nil_append,
    List.rotate_eq_drop_append_take (n := f.idxOf v) (Nat.le_of_lt hlt),
    List.drop_eq_getElem_cons hlt, List.getElem_idxOf hlt]

/-- rotateTo 的轨道坐标（getD 形）：第 j 元 = (idx v + j) mod len 处（j < len）。 -/
private theorem rotateToGetD {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {f : List α} {v : α} (hnd : f.Nodup) (hv : v ∈ f) (j : ℕ) (hj : j < f.length) :
    (Kepler.Text.Reduction3.rotateTo f v).getD j v
      = f.getD ((f.idxOf v + j) % f.length) v := by
  have hpos : 0 < f.length := List.length_pos_of_mem hv
  rw [rotateTo_eq_rotate hv,
    getD_eq_getElem_of_lt (show j < (f.rotate (f.idxOf v)).length by
      rwa [List.length_rotate]),
    List.getElem_rotate f (f.idxOf v) j (by rwa [List.length_rotate]),
    getD_eq_getElem_of_lt (Nat.mod_lt _ hpos),
    Nat.add_comm j (f.idxOf v)]

/-- nextEl 的下标形：`f.idxOf (nextEl f x) = (f.idxOf x + 1) % f.length`。 -/
private theorem nextElIdxOf [BEq α] [LawfulBEq α] [DecidableEq α] {f : List α} {x : α}
    (hnd : f.Nodup) (hx : x ∈ f) :
    f.idxOf (Kepler.Assembly.nextEl f x) = (f.idxOf x + 1) % f.length := by
  have hlt := idxOfLt hx
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

/-- 单步循环 filter 不变：x 居 f 的循环位置且 x ∈ r ⇒ 旋转 ix 与 ix+1 的
滤除相等（newvertex_alt 的旋转步核心；全在 take/drop 上做，免 rotate 位证）。 -/
private theorem filterRotateStep [BEq α] [LawfulBEq α] [DecidableEq α] {f : List α}
    (hnd : f.Nodup) {x : α} (hx : x ∈ f) (r : List α) (hxr : x ∈ r) :
    (f.rotate (f.idxOf x)).filter (fun d => decide (d ∉ r))
      = (f.rotate (f.idxOf x + 1)).filter (fun d => decide (d ∉ r)) := by
  have hlt := idxOfLt hx
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

/-- **newvertex_alt 核心**（HOL reduction2.hl:620-660）：x 旋转与 w = nextEl f x
旋转经双重点成员滤除后相等（x,w ∈ r 各杀一处）。 -/
private theorem rotateToFilterSwap {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    {f : List α} {x : α} (hnd : f.Nodup) (hx : x ∈ f) {r : List α} (hxr : x ∈ r)
    (hwr : Kepler.Assembly.nextEl f x ∈ r) :
    (Kepler.Text.Reduction3.rotateTo f x).filter (fun d => decide (d ∉ r))
      = (Kepler.Text.Reduction3.rotateTo f (Kepler.Assembly.nextEl f x)).filter
        (fun d => decide (d ∉ r)) := by
  have hw : Kepler.Assembly.nextEl f x ∈ f := nextEl_mem_of_mem hx
  rw [rotateTo_eq_rotate hx, rotateTo_eq_rotate hw, nextElIdxOf hnd hx,
    List.rotate_mod]
  exact filterRotateStep hnd hx r hxr


/-! ## §2 face_diff_r / le_y_in_r 结论级（HOL :489/:690 的免移植形） -/

/-- **HOL `rtrans_diff_r`**（reduction2.hl:489）：r' 的 r-差恰为 face 新弧
（between f_y y z；S 段 ⊆ r 全滤除、face 弧 ∉ r 全保留）。 -/
private theorem rtransFilterEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))
      = between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x) := by
  have hun : r.Nodup := (normalListUniqNonnil hm.1.2.1 hm.1.2.2.1).1
  have hy := ytransMemRtrans L hL hgn hm hf
  have hz := zMemRtransClean L hL hgn hunL hm hf
  rw [rtransCat L N r x hf hun, List.filter_append, List.filter_append,
    List.filter_append,
    show (List.filter (fun d => decide (d ∉ r)) [lZSpine L N r x]) = [] from by simp [hz],
    show (List.filter (fun d => decide (d ∉ r)) [lYSpine L r x]) = [] from by simp [hy],
    show (List.filter (fun d => decide (d ∉ r))
        (between r (lZSpine L N r x) (lYSpine L r x))) = [] from by
      rw [List.filter_eq_nil_iff]
      intro d hd
      simp [betwnMem hd],
    List.nil_append, List.nil_append, List.nil_append]
  exact List.filter_eq_self.mpr (fun d hd => by
    simp [betwnNotInRtrans L hL hgn hunL hm hf hd])

/-- **HOL `le_y_in_r`**（reduction2.hl:690-780）轨道化形：w 起 face 轨道上
indexf ≤ l'm 的 dart ∈ r（NCVIBWU.l_y_rep_power_le + fListPowEqNextElPow +
indexfN 三件组装，免逐段移植）。 -/
private theorem leYInR (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    {x' : ℕ × ℕ} (hx'f : x' ∈ findFaceDarts L x)
    (hix : indexf (nextEl (findFaceDarts L x) x) x' (findFaceDarts L x) ≤ lMSpine L r x) :
    x' ∈ r := by
  have hxr : x ∈ r := hm.1.2.2.2.1
  have hnext : nextEl r x = fList L x := hm.1.2.2.2.2.2.1
  have hxd : x ∈ listOfDarts L :=
    normalListListOfDarts hm.1.2.1 x (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hxr⟩)
  have hxx : x ∈ findFaceDarts L x := (dart_in_face L x).mpr hxd
  have hndf : (findFaceDarts L x).Nodup := findFaceDarts_nodup hL.1 x
  have hwf : nextEl (findFaceDarts L x) x ∈ findFaceDarts L x := nextEl_mem_of_mem hxx
  have h1 : (nextEl (findFaceDarts L x))^[indexf (nextEl (findFaceDarts L x) x) x'
      (findFaceDarts L x)] (nextEl (findFaceDarts L x) x) = x' :=
    indexfN hwf hx'f hndf
  have h2 : (nextEl (findFaceDarts L x))^[indexf (nextEl (findFaceDarts L x) x) x'
      (findFaceDarts L x) + 1] x = x' := by
    rw [Function.iterate_succ_apply]
    exact h1
  have h3 : (fList L)^[indexf (nextEl (findFaceDarts L x) x) x'
      (findFaceDarts L x) + 1] x = x' := by
    rw [fListPowEqNextElPow L hL x hxx]
    exact h2
  have h4 : (nextEl r)^[indexf (nextEl (findFaceDarts L x) x) x'
      (findFaceDarts L x) + 1] x = x' := by
    rw [← aq10_lYRepPowerLe L r x hnext.symm
      (indexf (nextEl (findFaceDarts L x) x) x' (findFaceDarts L x)) hix]
    exact h3
  rw [← h4]
  exact orbitMem hxr _


/-- **news 三段分解**（face_diff_r 结论级弱化形；HOL :843-1040 的 rest 免识别）：
`newvertex = MAP FST (betwn f y z) ++ rest`。 -/
private theorem newsSplit (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hunL : ∀ l ∈ L, l.Nodup) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    ∃ rest : List ℕ,
      Kepler.Text.Reduction3.newvertex L r x
        = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).map
            (fun d => d.1) ++ rest := by
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
  set G := (findFaceDarts L x).rotate ((findFaceDarts L x).idxOf (nextEl (findFaceDarts L x) x))
    with hG
  have hndG : G.Nodup := by rw [hG]; exact List.nodup_rotate.mpr hndf
  have hyG : lYSpine L r x ∈ G := by rw [hG]; exact List.mem_rotate.mpr hyf
  have hzG : lZSpine L N r x ∈ G := by rw [hG]; exact List.mem_rotate.mpr hzf
  have hpG : G.idxOf (lYSpine L r x) = lMSpine L r x := by
    rw [hG]
    exact Eq.trans (idxOfRotateEqIndexf hndf hpos hwf hyf)
      (indexfYtransEqLm L hL hgn hunL hm hf)
  have hbetw : between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x)
      = between G (lYSpine L r x) (lZSpine L N r x) := by
    rw [hG]
    exact betwnRot hndf hyf hzf hyne _
  -- 前缀杀段：take (p+1) G ⊆ r
  have takeKill : ∀ d ∈ G.take (G.idxOf (lYSpine L r x) + 1), d ∈ r := by
    intro d hd
    obtain ⟨j, hj, hjd⟩ := List.mem_take_iff_getElem.mp hd
    have hjG : j < G.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have hidx : G.idxOf d = j := by
      have h := hndG.idxOf_getElem j hjG
      rwa [hjd] at h
    have hdf : d ∈ findFaceDarts L x := by
      rw [hG] at hd
      exact List.mem_rotate.mp (List.mem_of_mem_take hd)
    have hjle : j ≤ lMSpine L r x := by
      have h1 : j < G.idxOf (lYSpine L r x) + 1 := lt_of_lt_of_le hj (Nat.min_le_left _ _)
      rw [hpG] at h1
      omega
    refine leYInR L hL hgn hunL hm hf hdf ?_
    have hix2 : indexf (nextEl (findFaceDarts L x) x) d (findFaceDarts L x) = List.idxOf d G := by
      rw [hG]
      exact (idxOfRotateEqIndexf hndf hpos hwf hdf).symm
    exact le_of_eq_of_le (hix2.trans hidx) hjle
  -- 段 ∉ r：between G y z ⊆ 补集
  have hkeep : ∀ d ∈ between G (lYSpine L r x) (lZSpine L N r x), d ∉ r := by
    intro d hd
    refine betwnNotInRtrans L hL hgn hunL hm hf ?_
    rw [findFaceDarts_congr_of_mem hL.1 hxd hyf, hbetw]
    exact hd
  have hkill : (G.take (G.idxOf (lYSpine L r x) + 1)).filter (fun d => decide (d ∉ r)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro d hd
    simp [takeKill d hd]
  have hsplit : G = G.take (G.idxOf (lYSpine L r x) + 1) ++ G.drop (G.idxOf (lYSpine L r x) + 1) :=
    (List.take_append_drop _ G).symm
  have hcore : ∃ restD : List (ℕ × ℕ),
      (Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) x).filter (fun d => decide (d ∉ r))
        = between (findFaceDarts L x) (lYSpine L r x) (lZSpine L N r x) ++ restD := by
    have hsw := rotateToFilterSwap hndf hxx hxr hwr
    have hrotG : Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) (nextEl (findFaceDarts L x) x) = G :=
      Eq.trans (rotateTo_eq_rotate hwf) hG.symm
    by_cases hpq : G.idxOf (lYSpine L r x) < G.idxOf (lZSpine L N r x)
    · refine ⟨(List.drop (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1))
          (List.drop (G.idxOf (lYSpine L r x) + 1) G)).filter (fun d => decide (d ∉ r)), ?_⟩
      rw [hsw, hrotG, hbetw]
      have hbtd : between G (lYSpine L r x) (lZSpine L N r x)
          = (List.drop (G.idxOf (lYSpine L r x) + 1) G).take
              (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1)) := by
        rw [betwnTakeDrop hndG hzG, if_pos hpq]
      rw [hbtd]
      conv_lhs => rw [hsplit]
      rw [List.filter_append, hkill, List.nil_append]
      have hfapp : (G.drop (G.idxOf (lYSpine L r x) + 1)).filter (fun d => decide (d ∉ r))
          = ((List.drop (G.idxOf (lYSpine L r x) + 1) G).take
                (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1))
              ++ (List.drop (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1))
                    (List.drop (G.idxOf (lYSpine L r x) + 1) G))).filter
              (fun d => decide (d ∉ r)) := by
        conv_lhs => rw [← List.take_append_drop
          (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1))
          (List.drop (G.idxOf (lYSpine L r x) + 1) G)]
      rw [hfapp, List.filter_append]
      have hkeepf : ((List.drop (G.idxOf (lYSpine L r x) + 1) G).take
            (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1))).filter
            (fun d => decide (d ∉ r))
          = (List.drop (G.idxOf (lYSpine L r x) + 1) G).take
              (G.idxOf (lZSpine L N r x) - (G.idxOf (lYSpine L r x) + 1)) := by
        rw [List.filter_eq_self]
        intro d hd
        simp [hkeep d (hbtd.symm ▸ hd)]
      rw [hkeepf]
    · by_cases hq0 : G.idxOf (lZSpine L N r x) = 0
      · refine ⟨[], ?_⟩
        rw [hsw, hrotG, hbetw]
        have hbtd : between G (lYSpine L r x) (lZSpine L N r x) = G.drop (G.idxOf (lYSpine L r x) + 1) := by
          rw [betwnTakeDrop hndG hzG, if_neg hpq, hq0, List.take_zero, List.append_nil]
        rw [hbtd, List.append_nil]
        have hkill2 : ∀ d ∈ G.drop (G.idxOf (lYSpine L r x) + 1), d ∉ r := by
          intro d hd
          exact hkeep d (hbtd.symm ▸ hd)
        conv_lhs => rw [hsplit]
        rw [List.filter_append, hkill, List.nil_append]
        rw [List.filter_eq_self.mpr (fun d hd => by simp [hkill2 d hd])]
      · exfalso
        have hne : G.take (G.idxOf (lZSpine L N r x)) ≠ [] := by
          rw [← List.length_pos_iff_ne_nil, List.length_take]
          have h1 : G.idxOf (lZSpine L N r x) < G.length := List.idxOf_lt_length_iff.mpr hzG
          have : 0 < G.idxOf (lZSpine L N r x) := Nat.pos_of_ne_zero hq0
          omega
        obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
        have hdr : d ∈ r := by
          refine takeKill d ?_
          have hd' : d ∈ G.take (G.idxOf (lYSpine L r x) + 1) := by
            obtain ⟨j, hj, hjd⟩ := List.mem_take_iff_getElem.mp hd
            rw [List.mem_take_iff_getElem]
            refine ⟨j, ?_, hjd⟩
            have h1 : j < G.idxOf (lZSpine L N r x) := lt_of_lt_of_le hj (Nat.min_le_left _ _)
            have h2 : G.idxOf (lZSpine L N r x) ≤ G.idxOf (lYSpine L r x) := by omega
            omega
          exact hd'
        have hdb : d ∈ between G (lYSpine L r x) (lZSpine L N r x) := by
          rw [betwnTakeDrop hndG hzG, if_neg hpq]
          exact List.mem_append_right _ hd
        exact hkeep d hdb hdr
  obtain ⟨restD, hrestD⟩ := hcore
  refine ⟨restD.map (fun d => d.1), ?_⟩
  rw [show Kepler.Text.Reduction3.newvertex L r x
      = ((Kepler.Text.Reduction3.rotateTo (findFaceDarts L x) x).filter
          (fun d => decide (d ∉ r))).map (fun d => d.1) from rfl,
    hrestD, List.map_append, findFaceDarts_congr_of_mem hL.1 hxd hyf]


/-! ## §3 take 数算 + 无条件主定理 -/

/-- `range'` 的 take 前缀形（`l ≤ L` 时截取即低段）。 -/
private theorem take_range'_eq (n l L : ℕ) (h : l ≤ L) :
    (List.range' n L).take l = List.range' n l := by
  conv_lhs => rw [show L = l + (L - l) from (Nat.add_sub_of_le h).symm]
  rw [← List.range'_append, List.take_append,
    List.take_of_length_le (by rw [List.length_range']),
    List.length_range', Nat.sub_self, List.take_zero, List.append_nil]

/-- `range'` 的集形：`setOfListNatSpine (range' n l) = {i | n ≤ i < n+l}`。 -/
private theorem setOfListNatSpine_range' (n l : ℕ) :
    setOfListNatSpine (List.range' n l) = {i : ℕ | n ≤ i ∧ i < n + l} := by
  ext i
  show i ∈ List.range' n l ↔ n ≤ i ∧ i < n + l
  rw [List.mem_range']
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨i - n, by omega, by omega⟩

/-- 件1 私件 `rtransSpineEqSplit2` 的同款重推导（¬final 时 r' = split.2）。 -/
private theorem rtransSpineEqSplit2' (L : fgraph ℕ) (N : List (List (ℕ × ℕ)))
    (r : List (ℕ × ℕ)) (x : ℕ × ℕ) (hf : ¬finalListSpine L r) :
    rtransSpine L N r x 1 = (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
      (lYSpine L r x) (prevEl r (lZSpine L N r x))).2 := by
  show ((transformListSpine L x)^[1] (N, r)).2 = _
  rw [Function.iterate_one]
  simp only [transformListSpine, if_neg hf]

/-- 件1 私件 `leSubOneIff` 的同款重推导。 -/
private theorem leSubOneIff' {a b : ℕ} (hb : 1 ≤ b) : a ≤ b - 1 ↔ a < b := by
  rcases b with _ | c
  · exact absurd hb (by simp)
  · show a ≤ c ↔ a < c + 1
    exact Nat.lt_succ_iff.symm

/-- **HOL `elements_of_list_ntrans` 无条件形**（reduction2.hl:1042-1136 全量；
hbridge 槽由 news 前缀分解 + take 数算闭合，case B 直接 apply 件1
元素表定理，case A 走 LEBHIRJ 组装段 + v = [] 退化的计数相等）。 -/
theorem elementsOfListNtransTop
    (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hrre : Kepler.Text.Reduction5.rRtransEq L N r x)
    (hm : MarkedListSpineFull hL N r x)
    (hnvp : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hold : elementsOfList (Kepler.Text.Reduction5.quotientList L N)
      = {i : ℕ | i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1}) :
    elementsOfList (Kepler.Text.Reduction5.quotientList L (ntransSpine L N r x 1))
      = {i : ℕ | i ≤ ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length
        - 1} := by
  by_cases hfin : finalListSpine L r
  · rw [ntransId L N r x hfin]
    exact hold
  · -- 环境派生
    have hunL : ∀ l ∈ L, l.Nodup := (simpleHypermapUniq L hL hgn).mp hm.1.1.simple
    have hnews : Kepler.Text.Reduction3.newvertex L r x
        = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
            (Kepler.Text.Reduction3.newvertex L r x).length := by
      have h := hnvp
      rw [show Kepler.Text.Reduction3.newvertexPrepped L N r x =
          (finalListSpine L r ∨ Kepler.Text.Reduction3.newvertex L r x
            = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
                (Kepler.Text.Reduction3.newvertex L r x).length) from rfl] at h
      exact h.resolve_left hfin
    obtain ⟨rest, hrest⟩ := newsSplit L hL hgn hunL hm hfin
    by_cases hvE : ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
        (fun d => d.1) = []
    · -- **case A**（v = []，HOL 1075 + 1128-1136）：LEBHIRJ 组装段照搬 + 计数相等
      have hrnd : r.Nodup := uniqFlattenUniq N hm.1.2.1.1 r hm.1.2.2.1
      have hnspN : NormalListSpine hL N := hm.1.2.1
      have hnsp' : NormalListSpine hL (ntransSpine L N r x 1) := aqiunpp1_top L hL hgn hm
      have hEs : elementsOfList (quotientListSpine L N)
          = setOfListNatSpine (N.flatten.map (fun d => d.1)) :=
        quotientListElements L hL hnspN
      have hEs' : elementsOfList (quotientListSpine L (ntransSpine L N r x 1))
          = setOfListNatSpine ((ntransSpine L N r x 1).flatten.map (fun d => d.1)) :=
        quotientListElements L hL hnsp'
      have hn1 : 1 ≤ (N.flatten.map (fun d => d.1)).dedup.length := by
        by_contra h0
        have h0' : (N.flatten.map (fun d => d.1)).dedup.length = 0 := by omega
        have hd0 : (N.flatten.map (fun d => d.1)).dedup = [] :=
          List.length_eq_zero_iff.mp h0'
        have hfe : N.flatten.map (fun d => d.1) = [] := (List.dedup_eq_nil _).mp hd0
        have hxfn : x.1 ∈ N.flatten.map (fun d => d.1) :=
          List.mem_map.mpr ⟨x, List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hm.1.2.2.2.1⟩, rfl⟩
        exact absurd hxfn (by rw [hfe]; simp)
      have hOLDp : ∀ i : ℕ, i ∈ N.flatten.map (fun d => d.1) ↔
          i < (N.flatten.map (fun d => d.1)).dedup.length := by
        intro i
        have h1 : elementsOfList (Kepler.Text.Reduction5.quotientList L N)
            = setOfListNatSpine (N.flatten.map (fun d => d.1)) := by
          rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]; exact hEs
        have h2 := hold
        rw [h1] at h2
        have hi := congrArg (fun S : Set ℕ => i ∈ S) h2
        have hraw : i ∈ N.flatten.map (fun d => d.1) ↔
            i ≤ (N.flatten.map (fun d => d.1)).dedup.length - 1 := by
          simpa [setOfListNatSpine, Set.mem_setOf_eq] using hi
        exact hraw.trans (leSubOneIff' hn1)
      have hvFalse : ∀ i : ℕ, i ∈ ((rtransSpine L N r x 1).filter
          (fun d => decide (d ∉ r))).map (fun d => d.1) ↔ False := by
        intro i
        rw [hvE]
        simp
      have hy : lYSpine L r x ∈ r := ytransMemRtrans L hL hgn hm hfin
      have hz : lZSpine L N r x ∈ r := zMemRtransClean L hL hgn hunL hm hfin
      have hy1 : nextEl r (lYSpine L r x) ∈ r := nextEl_mem_of_mem hy
      have hz1 : prevEl r (lZSpine L N r x) ∈ r := prevEl_mem_of_mem hz
      have hnextz1 : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
        nextElPrevElUniq hrnd _
      have hcat : rtransSpine L N r x 1
          = ((([lZSpine L N r x] ++ between r (lZSpine L N r x) (lYSpine L r x))
              ++ [lYSpine L r x]) ++ between (findFaceDarts L (lYSpine L r x))
                (lYSpine L r x) (lZSpine L N r x)) :=
        rtransCat L N r x hfin hrnd
      obtain ⟨N₁, N₂, hN, hnot, hflat⟩ := aq1b_flattenNtrans1 L hL hgn hunL hm hfin
      have hNflat : N.flatten = N₁.flatten ++ (r ++ N₂.flatten) := by
        rw [hN, List.flatten_append, List.flatten_cons]
      have memfn : ∀ d ∈ N.flatten, d.1 ∈ N.flatten.map (fun d => d.1) :=
        fun d hd => List.mem_map.mpr ⟨d, hd, rfl⟩
      have sCase : ∀ d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).2,
          d.1 ∈ N.flatten.map (fun d => d.1) ∨
          d.1 ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1) := by
        intro d hd
        by_cases hdr : d ∈ r
        · exact Or.inl (memfn d (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hdr⟩))
        · refine Or.inr (List.mem_map.mpr ⟨d, ?_, rfl⟩)
          rw [rtransSpineEqSplit2' L N r x hfin]
          exact List.mem_filter.mpr ⟨hd, decide_eq_true_iff.mpr hdr⟩
      have fCase : ∀ d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))).1,
          d.1 ∈ N.flatten.map (fun d => d.1) ∨
          d.1 ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1) := by
        intro d hd
        have hf1 := split1Unfold L r (findFaceDarts L (lYSpine L r x))
          (lYSpine L r x) (prevEl r (lZSpine L N r x))
        rw [hnextz1] at hf1
        rw [hf1] at hd
        rcases List.mem_append.mp hd with hd | hd
        · rw [List.mem_reverse] at hd
          obtain ⟨blk, hblkm, hdblk⟩ := List.mem_flatten.mp hd
          obtain ⟨d₀, hd₀w, hd₀blk⟩ := List.mem_map.mp hblkm
          have hdart : d₀ ∈ (hypermapOfList L hL).darts :=
            List.mem_toFinset.mpr (mem_darts_of_mem_findFace L (betwnMem hd₀w))
          have hfsteq : d.1 = d₀.1 :=
            ndSpineFstEq L hL hgn hdart (hd₀blk ▸ hdblk)
          have hd₀nr : d₀ ∉ r := betwnNotInRtrans L hL hgn hunL hm hfin hd₀w
          refine Or.inr ?_
          rw [hfsteq]
          refine List.mem_map.mpr ⟨d₀, List.mem_filter.mpr ⟨?_,
            decide_eq_true_iff.mpr hd₀nr⟩, rfl⟩
          rw [hcat]
          exact List.mem_append_right _ hd₀w
        · refine Or.inl ?_
          have hin : d ∈ r := by
            rcases List.mem_append.mp hd with hd' | hd'
            · rcases List.mem_append.mp hd' with hd' | hb
              · simp only [List.mem_cons] at hd'
                rcases hd' with rfl | hnil
                · exact hy1
                · exact absurd hnil (by simp)
              · exact betwnMem hb
            · simp only [List.mem_cons] at hd'
              rcases hd' with rfl | hnil
              · exact hz1
              · exact absurd hnil (by simp)
          exact memfn d (List.mem_flatten.mpr ⟨r, hm.1.2.2.1, hin⟩)
      have hsub : ∀ i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1),
          i ∈ N.flatten.map (fun d => d.1) ∨
          i ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1) := by
        intro i hi
        obtain ⟨d, hdf, hdi⟩ := List.mem_map.mp hi
        rw [hflat] at hdf
        rcases List.mem_append.mp hdf with hdf | hdF
        · rcases List.mem_append.mp hdf with hdf | hdc
          · rcases List.mem_append.mp hdf with hdf | hds
            · refine Or.inl ?_
              rw [← hdi, hNflat]
              exact List.mem_map.mpr ⟨d, List.mem_append_left _ hdf, rfl⟩
            · exact hdi ▸ sCase d hds
          · refine Or.inl ?_
            rw [← hdi, hNflat]
            exact List.mem_map.mpr ⟨d,
              List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hdc))), rfl⟩
        · exact hdi ▸ fCase d hdF
      have hsup : ∀ i ∈ N.flatten.map (fun d => d.1),
          i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) := by
        intro i hi
        obtain ⟨d, hdf, hdi⟩ := List.mem_map.mp hi
        rw [hNflat] at hdf
        rcases List.mem_append.mp hdf with hdf | hdf
        · refine List.mem_map.mpr ⟨d, ?_, hdi⟩
          rw [hflat]
          exact List.mem_append.mpr (Or.inl
            (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hdf)))))
        rcases List.mem_append.mp hdf with hdf | hdf
        · have hdN' : d ∈ (ntransSpine L N r x 1).flatten := by
            have hcov := betwn_or_betwn_cover hrnd (prevEl r (lZSpine L N r x))
              (lYSpine L r x) hdf
            rw [hnextz1] at hcov
            have hto : d ∈ rtransSpine L N r x 1 ∨
                d ∈ (splitNormalListSpine L r (findFaceDarts L (lYSpine L r x))
                  (lYSpine L r x) (prevEl r (lZSpine L N r x))).1 := by
              rcases List.mem_append.mp hcov with hcov | hcov
              · refine Or.inl ?_
                rw [hcat]
                exact List.mem_append_left _ hcov
              · refine Or.inr ?_
                exact List.mem_append_right _ hcov
            rcases hto with hto | hdF
            · exact List.mem_flatten.mpr ⟨rtransSpine L N r x 1,
                aq6 L hL N r x hgn hm, hto⟩
            · rw [hflat]
              exact List.mem_append_right _ hdF
          exact List.mem_map.mpr ⟨d, hdN', hdi⟩
        · refine List.mem_map.mpr ⟨d, ?_, hdi⟩
          rw [hflat]
          exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hdf)))
      have hsupv : ∀ i ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1),
          i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) := by
        intro i hi
        obtain ⟨d, hdF, hdi⟩ := List.mem_map.mp hi
        refine List.mem_map.mpr ⟨d, ?_, hdi⟩
        exact List.mem_flatten.mpr ⟨rtransSpine L N r x 1, aq6 L hL N r x hgn hm,
          (List.mem_filter.mp hdF).1⟩
      have hpoint : ∀ i : ℕ, i ∈ (ntransSpine L N r x 1).flatten.map (fun d => d.1) ↔
          i ∈ N.flatten.map (fun d => d.1) ∨
          i ∈ ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1) :=
        fun i => ⟨fun him => hsub i him, fun hv => hv.elim (hsup i) (hsupv i)⟩
      have htof : ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).toFinset
          = (N.flatten.map (fun d => d.1)).toFinset := by
        ext i
        simp only [List.mem_toFinset]
        rw [hpoint i]
        constructor
        · rintro (h | h)
          · exact h
          · rw [hvE] at h
            exact absurd h (by simp)
        · exact fun h => Or.inl h
      have hK : ((ntransSpine L N r x 1).flatten.map (fun d => d.1)).dedup.length
          = (N.flatten.map (fun d => d.1)).dedup.length := by
        rw [← List.card_toFinset, ← List.card_toFinset, htof]
      rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine, hEs', hK]
      ext i
      simp only [setOfListNatSpine, Set.mem_setOf_eq]
      rw [hpoint i, hvFalse i, hOLDp i]
      simp only [or_false]
      exact (leSubOneIff' hn1).symm
    · -- **case B**（v ≠ []）：newsSplit + take 数算 + apply 件1
      have hvbetw : ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)
          = (between (findFaceDarts L (lYSpine L r x)) (lYSpine L r x) (lZSpine L N r x)).map
              (fun d => d.1) := by
        rw [rtransFilterEq L hL hgn hunL hm hfin]
      have htake : List.take ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)).length) (Kepler.Text.Reduction3.newvertex L r x)
          = ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
              (fun d => d.1) := by
        rw [hrest, hvbetw, List.take_left]
      have hlen_news : (Kepler.Text.Reduction3.newvertex L r x).length
          = ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
              (fun d => d.1)).length + rest.length) := by
        rw [hrest, hvbetw, List.length_append]
      have hv_eq : ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
            (fun d => d.1)
          = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
              ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
                (fun d => d.1)).length) := by
        calc ((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map (fun d => d.1)
            = List.take ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
                (fun d => d.1)).length) (Kepler.Text.Reduction3.newvertex L r x) := htake.symm
          _ = List.take ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
                (fun d => d.1)).length)
              (List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
                (Kepler.Text.Reduction3.newvertex L r x).length) := by
            conv_lhs => rw [hnews]
          _ = List.range' ((N.flatten.map (fun d => d.1)).dedup.length)
              ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
                (fun d => d.1)).length) := take_range'_eq _ _ _ (by omega)
      have hlpos : 0 < ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
          (fun d => d.1)).length) := List.length_pos_iff_ne_nil.mpr hvE
      refine elementsOfListNtrans L hL hgn hrre hm hnvp hold ⟨
        (N.flatten.map (fun d => d.1)).dedup.length
          + ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
              (fun d => d.1)).length) - 1, by omega, ?_⟩
      have hsetv : setOfListNatSpine (((rtransSpine L N r x 1).filter
          (fun d => decide (d ∉ r))).map (fun d => d.1))
          = {i : ℕ | (N.flatten.map (fun d => d.1)).dedup.length ≤ i ∧
              i ≤ (N.flatten.map (fun d => d.1)).dedup.length
                + ((((rtransSpine L N r x 1).filter (fun d => decide (d ∉ r))).map
                  (fun d => d.1)).length) - 1} := by
        rw [hv_eq, setOfListNatSpine_range']
        ext i
        simp only [Set.mem_setOf_eq]
        rw [List.length_range']
        omega
      exact hsetv

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.elementsOfListNtransTop
#print axioms Kepler.Text.TameSpine.newsSplit
#print axioms Kepler.Text.TameSpine.leYInR
