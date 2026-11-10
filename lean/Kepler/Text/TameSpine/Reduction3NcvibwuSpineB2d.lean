/-
  Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2d — W2-件2 Wave B2d：
  NCVIBWU-spine i=0 的弧位次刻划四件 + OHCGKFU-i0 槽形。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ tame_list.hl:2433 `betwn_take_drop` → §1 betwnPosGetElem
  │   （betwn 元的 s-绝对位次，线性/wrap 双支 mod 位移收口）；
  │ Ncvibwu.hl:131 `next_el_betwn_same` → §2 betwnSuccGetElem
  │   （弧内逐位 succ；本文件走位置路线，见 DIFFERS ④）；
  │ §3 betwnOrbit：共享弧轨道刻划 `(between s a b)[j] = (nextEl s)^[j+1] a`
  │   （§0 轨道枚举 + §1 位次直拼，无归纳、无 wrap 案析）；
  │ §4 hnest：OHCGKFU-spine i=0 的显式槽（三要素见该 DEF 注释）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（路线换轨，均有机器证据）────────────────────────────────
  │ ① §1 走 `getElem?`（Option 形）重写 + 双桥 `getElem?_eq_getElem`
  │   回 getElem：`betwnTakeDrop` 对含从属 getElem 位次证明的目标直接
  │   rw 会动机失败（战役雷区，J4 `getElemCongrList` 先例的 Option 化
  │   变体）——全部 take/drop/append 位移在 Option 上完成，末段一次桥回。
  │ ② §2 尾段不用 `simp only [nextEl]` 的 if 形，改用树内
  │   `nextEl_eq_getD : nextEl s x = s.getD ((s.idxOf x + 1) % s.length) x`
  │   ——mod 形把 headD/末位支整段吸收（该桥自身已含 hlast 案析）。
  │ ③ 全文件 `α : Type`（universe 0）：`nextElBetwnSame`
  │   （CoreSplitNormal:477）是 Type 0 件，无法在 Type u 直接实例。
  │ ④ §2 不走 `nextElBetwnSame` 直用：其 `between` 走
  │   `instBEqOfDecidableEq`（b2a 记档的 R1 默认实例不桥接本文件泛型
  │   实例），改位置路线（§1 双实例 + nextEl_eq_getD）；`hdm` 前提位保留。
  │ ⑤ §1/§3 的前提统一为 `j < |between s a b|`（弧内末位也成立），
  │   §2 的 j+1 位可直接改取 §1，无需 j+2 界。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入；既有文件零触碰。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3OhcgkfuSpineV0
import Kepler.Text.TameSpine.Reduction3CoreSplitNormal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl nextEl_mem_of_mem dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  getElem_idxOf getD_eq_getElem_of_lt nextEl_eq_getD)

variable {α : Type}

/-! ## §0 轨道枚举（B2c-p1 同款重推导） -/

/-- `(m % len + 1) % len = (m + 1) % len`。 -/
private theorem modSuccEqW (m len : ℕ) : (m % len + 1) % len = (m + 1) % len := by
  have h : m + 1 = len * (m / len) + (m % len + 1) := by
    have := Nat.div_add_mod m len
    omega
  rw [h, Nat.add_comm (len * (m / len)), Nat.add_mul_mod_self_left]

/-- getD 下标自反：`s.getD (s.idxOf a) a = a`。 -/
private theorem getDIdxOfSelfW [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    {a : α} (ha : a ∈ s) : s.getD (s.idxOf a) a = a := by
  rw [getD_eq_getElem_of_lt (List.idxOf_lt_length_iff.mpr ha), getElem_idxOf ha]

/-- getD 下标单射：`s.idxOf (s.getD (m % s.length) a) = m % s.length`。 -/
private theorem getDIdxEqW [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) (hpos : 0 < s.length) (m : ℕ) (a : α) :
    s.idxOf (s.getD (m % s.length) a) = m % s.length := by
  rw [getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  exact hnd.idxOf_getElem (m % s.length) (Nat.mod_lt _ hpos)

/-- **轨道枚举（getD 形）**：`(nextEl s)^[k] a = s.getD ((s.idxOf a + k) % s.length) a`。 -/
private theorem orbitGetElemW [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) (hpos : 0 < s.length) {a : α} (ha : a ∈ s) (k : ℕ) :
    (nextEl s)^[k] a = s.getD ((s.idxOf a + k) % s.length) a := by
  have hilt : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr ha
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, Nat.add_zero, Nat.mod_eq_of_lt hilt,
      getD_eq_getElem_of_lt hilt, getElem_idxOf ha]
  | succ k ih =>
    have hdmem : s.getD ((s.idxOf a + k) % s.length) a ∈ s := by
      have hm : (s.idxOf a + k) % s.length < s.length := Nat.mod_lt _ hpos
      rw [getD_eq_getElem_of_lt hm]
      exact List.getElem_mem hm
    have hidxm : s.idxOf (s.getD ((s.idxOf a + k) % s.length) a)
        = (s.idxOf a + k) % s.length := getDIdxEqW hnd hpos (s.idxOf a + k) a
    rw [Function.iterate_succ_apply', ih, nextEl_eq_getD hdmem, hidxm, modSuccEqW,
      show s.idxOf a + k + 1 = s.idxOf a + (k + 1) from by omega,
      getD_eq_getElem_of_lt (Nat.mod_lt _ hpos),
      getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]

/-! ## §1 弧位次刻划 -/

/-- betwn 元的 s-绝对位次（线性/wrap 双支，mod 位移收口）。
证走 Option 形（DIFFERS ①）：从属位次证明不入 rw 动机。 -/
theorem betwnPosGetElem [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    {a b : α} (hne : a ≠ b) (hnd : s.Nodup) (ha : a ∈ s) (hb : b ∈ s)
    {j : ℕ} (hj : j < (between s a b).length) :
    (between s a b)[j]'(by omega) =
      s[(s.idxOf a + 1 + j) % s.length]'(Nat.mod_lt _ (List.length_pos_of_mem ha)) := by
  have hpos : 0 < s.length := List.length_pos_of_mem ha
  have hlta : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr ha
  have hltb : s.idxOf b < s.length := List.idxOf_lt_length_iff.mpr hb
  have hopt : (between s a b)[j]? = s[(s.idxOf a + 1 + j) % s.length]? := by
    rw [betwnTakeDrop hnd hb]
    by_cases hlt : s.idxOf a < s.idxOf b
    · have hlen : ((s.drop (s.idxOf a + 1)).take
          (s.idxOf b - (s.idxOf a + 1))).length = s.idxOf b - (s.idxOf a + 1) := by
        rw [List.length_take, List.length_drop]
        omega
      have hjlen : j < s.idxOf b - (s.idxOf a + 1) := by
        have h := hj
        rw [betwnTakeDrop hnd hb, if_pos hlt, hlen] at h
        exact h
      rw [if_pos hlt, List.getElem?_take, List.getElem?_drop,
        if_pos hjlen, Nat.mod_eq_of_lt (by omega)]
    · have hBlen : (between s a b).length
          = (s.length - (s.idxOf a + 1)) + s.idxOf b := by
        rw [betwnTakeDrop hnd hb, if_neg hlt, List.length_append, List.length_drop,
          List.length_take, Nat.min_eq_left (by omega)]
      rw [if_neg hlt, List.getElem?_append, List.length_drop]
      split
      · rw [List.getElem?_drop, Nat.mod_eq_of_lt (by omega)]
      · rename_i hge
        rw [List.getElem?_take,
          if_pos (show j - (s.length - (s.idxOf a + 1)) < s.idxOf b by omega)]
        have hkL : (s.length - (s.idxOf a + 1)) + (s.idxOf a + 1) = s.length :=
          Nat.sub_add_cancel (by omega)
        have hkj : s.length - (s.idxOf a + 1) ≤ j := by omega
        have hmL : s.length ≤ s.idxOf a + 1 + j := by
          rw [show s.length = (s.length - (s.idxOf a + 1)) + (s.idxOf a + 1) from hkL.symm]
          omega
        have hk : s.idxOf a + 1 + (s.length - (s.idxOf a + 1)) = s.length := by omega
        have hkey : s.idxOf a + 1 + j
            = (j - (s.length - (s.idxOf a + 1))) + s.length := by
          calc s.idxOf a + 1 + j
              = s.idxOf a + 1 + (j - (s.length - (s.idxOf a + 1))
                  + (s.length - (s.idxOf a + 1))) := by rw [Nat.sub_add_cancel hkj]
            _ = (j - (s.length - (s.idxOf a + 1))) + (s.idxOf a + 1
                  + (s.length - (s.idxOf a + 1))) := by omega
            _ = (j - (s.length - (s.idxOf a + 1))) + s.length := by rw [hk]
        have hidx : (s.idxOf a + 1 + j) % s.length
            = j - (s.length - (s.idxOf a + 1)) := by
          rw [Nat.mod_eq_sub_mod hmL, Nat.sub_eq_of_eq_add hkey,
            Nat.mod_eq_of_lt (Nat.sub_lt_left_of_lt_add hkj
              (by omega : j < (s.length - (s.idxOf a + 1)) + s.length))]
        rw [hidx]
  rw [List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem (Nat.mod_lt _ hpos)] at hopt
  exact Option.some_inj.mp hopt

/-! ## §2 共享弧 succ -/

/-- betwn 的逐位 succ。DIFFERS ④：树内 `nextElBetwnSame` 的 `between`
走 `instBEqOfDecidableEq`（b2a 记档的 R1 默认实例不桥接泛型实例），
本件改**位置路线**（betwnPosGetElem 双实例 + nextEl_eq_getD mod 形），
`hdm` 保留为 HOL `next_el_betwn_same` 的 hnext 前提位（本证不消费）。 -/
theorem betwnSuccGetElem [BEq α] [LawfulBEq α] [DecidableEq α]
    {s : List α} {a b : α} (hne : a ≠ b) (hnd : s.Nodup) (ha : a ∈ s) (hb : b ∈ s)
    {j : ℕ} (hj1 : j + 1 < (between s a b).length)
    (hdm : nextEl s ((between s a b)[j]'(by omega)) ∈ between s a b) :
    nextEl s ((between s a b)[j]'(by omega)) = (between s a b)[j + 1]'(by omega) := by
  have hpos : 0 < s.length := List.length_pos_of_mem ha
  have hBj := betwnPosGetElem hne hnd ha hb (by omega : j < (between s a b).length)
  have hBj1 := betwnPosGetElem hne hnd ha hb hj1
  have hdmem' : (between s a b)[j]'(by omega) ∈ s := by
    rw [hBj]
    exact List.getElem_mem (Nat.mod_lt _ hpos)
  have hidxj : s.idxOf ((between s a b)[j]'(by omega))
      = (s.idxOf a + 1 + j) % s.length := by
    rw [hBj]
    exact hnd.idxOf_getElem (i := (s.idxOf a + 1 + j) % s.length) (Nat.mod_lt _ hpos)
  rw [nextEl_eq_getD hdmem', hidxj, modSuccEqW,
    getD_eq_getElem_of_lt (Nat.mod_lt _ hpos), hBj1,
    show s.idxOf a + 1 + j + 1 = s.idxOf a + 1 + (j + 1) from by omega]

/-! ## §3 共享弧轨道刻划 -/

/-- betwn 元的轨道刻划：`(between s a b)[j] = (nextEl s)^[j+1] a`
（§1 位次 + §0 轨道枚举直拼；无归纳、无 wrap 案析）。 -/
theorem betwnOrbit [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    {a b : α} (hne : a ≠ b) (hnd : s.Nodup) (ha : a ∈ s) (hb : b ∈ s)
    {j : ℕ} (hj : j < (between s a b).length) :
    (between s a b)[j]'(by omega) = (nextEl s)^[j + 1] a := by
  have hpos : 0 < s.length := List.length_pos_of_mem ha
  have hbpos := betwnPosGetElem hne hnd ha hb hj
  have horb := orbitGetElemW hnd hpos ha (j + 1)
  rw [hbpos, horb, ← getD_eq_getElem_of_lt (d := a) (Nat.mod_lt _ hpos),
    show s.idxOf a + 1 + j = s.idxOf a + (j + 1) from by omega]

/-! ## §4 OHCGKFU-i0 显式槽（hnest） -/

/-- **显式槽 `hnest`**（OHCGKFU-spine i=0 的头段弧嵌套前提）。

三要素（B2e 填充对表，机械 0 行收口核对）：
- **槽名**：`hnest`；
- **填法**：state-1 `aqs_nextMarkCaseMem` 平行论证（JcajyduAqLeaf12T:130，
  spine 公开）供 `w ∈ between r z1 y` 的弧嵌套，经 §1–§3 位置件
  （betwnPosGetElem/betwnSuccGetElem/betwnOrbit）转移到 face 段；
- **目标定理名**：`ohcgkfuSpineV0`（B2e 拼装：hnest 填后与 B1 的
  `ncvibwuSpineV0FPart` 并集即头段 ∪ F-弧 = spine-i0 成员性）。

语义：face 段 `w..y`（= `(nextEl f)^[1..lM+1] x`，f = findFaceDarts L x）
整段落在变换后 r'（= rtransSpine L N r x 1）的 `l'z → l'y` 弧内。 -/
def hnest (L : fgraph ℕ) (N : List (List (ℕ × ℕ))) (r : List (ℕ × ℕ))
    (x : ℕ × ℕ) : Prop :=
  ∀ j : ℕ, j ≤ lMSpine L r x →
    (nextEl (findFaceDarts L x))^[j + 1] x ∈
      between (rtransSpine L N r x 1) (lZSpine L N r x) (lYSpine L r x)

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.orbitGetElemW
#print axioms Kepler.Text.TameSpine.betwnPosGetElem
#print axioms Kepler.Text.TameSpine.betwnSuccGetElem
#print axioms Kepler.Text.TameSpine.betwnOrbit
#print axioms Kepler.Text.TameSpine.hnest
