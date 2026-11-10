/-
  Kepler.Text.TameSpine.Reduction3HbridgeElim — W2-件1a：`hbridge` 槽闭合
  （`elements_of_list_ntrans` 的无条件形，HOL reduction2.hl:1042-1136 全量）。

  ┌─ 状态（本轮 = 止损口径半成品交付）─────────────────────────────
  │ 已交付：§0 泛型旋转/轨道工具层 8 件（岛编 RC=0 零 error；探针
  │ orbitEnumGetD/idxOfRotateEqIndexf/getDIdxEq = 标准三、modSuccEq =
  │ {propext, Quot.sound}，零 sorryAx —— compile_1a_probe.log）。
  │ 未交付：§1 主装 `elementsOfListNtransTop`（见下方 §1 路线图；
  │ §0+§1 实测估 500 行 > 450 止损线，按 AGENTS §7 交班）。
  └────────────────────────────────────────────────────────────────

  ┌─ 与已落库件1（011c0451，Reduction3ElementsOfListNtrans）的关系 ─
  │ 件1 主定理携带显式前提 `hbridge`（HOL 1085-1089 ENOUGH_TO_SHOW 内
  │ 切口：∃k, n ≤ k ∧ set(MAP FST (filter (¬MEM r) r')) = n..k，
  │ n = fn.dedup.length、r' = rtrans L N r x 1）。本件目标：由
  │ `newvertexPrepped`（news = List.range' n …）闭合它，得无条件形。
  │ §1 路线图（本轮侦察定型，下一波零侦察直做）：
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
import Kepler.Text.ChainBridgeParts
import Kepler.Text.Reduction3DefsNewVertex
import Kepler.Text.Reduction5Base

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between splitAt)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts)
open Kepler.Text.TameLp (elementsOfList GoodListNodesTl nextEl_mem_of_mem
  prevEl_mem_of_mem hypermapOfList dart_in_face findFaceDarts_congr_of_mem
  mem_darts_of_mem_findFace nextEl_eq_getD getD_eq_getElem_of_lt)

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
end Kepler.Text.TameSpine
