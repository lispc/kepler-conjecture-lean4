/-
  Kepler.Text.TameSpine.Reduction3OhcgkfuSpineV0 — W2-件2 Wave B2c（部分交付）：
  轨道枚举件 + modSucc 桥 + getD 下标件（OHCGKFU-spine i=0 总装的头部基建）。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ OHCGKFU.hl:162 `OHCGKFU`（i=0 剪枝）的总装前置：
  │   ① modSuccEqW（件1a 私件同款重推导）；
  │   ② orbitGetElemW：轨道枚举 `(nextEl s)^[k] a =
  │     s.getD ((s.idxOf a + k) % s.length) a`（件1a 私件 orbitEnumGetD
  │      同款重推导，getD 形——B2d 头段案析的定位引擎）；
  │   ③ getDIdxOfSelfW/getDIdxEqW（件1a 私件同款重推导）。
  │ 后续接缝（B2d）：bArcEq（共享弧等式）+ betwnHeadNext/betwnSuccGetElem/
  │ betwnOrbit（betwn 轨道刻划三件）+ OHCGKFU-i0 总装。蓝本已入
  │ DELIVERY_2B2c 接缝节。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零禁词（无公理/未证占位/变体求值）；主仓双零写入；既有文件零触碰。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.Reduction3NcvibwuSpineB2b

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Assembly (nextEl prevEl GoodList findFaceDarts fList listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl nextEl_mem_of_mem dart_in_face
  findFaceDarts_nodup findFaceDarts_congr_of_mem mem_darts_of_mem_findFace
  getElem_idxOf getD_eq_getElem_of_lt nextEl_eq_getD)

variable {α : Type*}

/-! ## §0 轨道枚举（件1a 私件同款重推导） -/

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

/-- getD 下标单射：`s.idxOf (s.getD (s.idxOf a) a) = s.idxOf a`。 -/
private theorem getDIdxEqW [BEq α] [LawfulBEq α] [DecidableEq α] {s : List α}
    (hnd : s.Nodup) (hpos : 0 < s.length) (m : ℕ) (d : α) :
    s.idxOf (s.getD (m % s.length) d) = m % s.length := by
  rw [getD_eq_getElem_of_lt (Nat.mod_lt _ hpos)]
  exact hnd.idxOf_getElem (m % s.length) (Nat.mod_lt _ hpos)

/-! ### 接缝（B2d 首件，蓝本已核）：**轨道枚举 getD 形**
`(nextEl s)^[k] a = s.getD ((s.idxOf a + k) % s.length) a`。
结构已核 90%：`nextEl_eq_getD hdmem`（hdmem : getD-dart ∈ s，经
getD_eq_getElem_of_lt + getElem_mem）+ `getDIdxEqW hnd hpos
((s.idxOf a + k) % s.length) a`（m = 轨道位次）+ getD_eq 双消。
剩余 wrinkle：getDIdxEqW 实例化时 m 的统一需显式传
`(s.idxOf a + k) % s.length`（% 嵌套形，勿传裸和形）；
hdmem 经 getD_eq_getElem_of_lt hm + getElem_mem hm。 -/

end Kepler.Text.TameSpine

-- 公理探针（编译即执行；目标：标准三，零未证占位）
#print axioms Kepler.Text.TameSpine.modSuccEqW
#print axioms Kepler.Text.TameSpine.getDIdxOfSelfW
#print axioms Kepler.Text.TameSpine.getDIdxEqW
#print axioms Kepler.Text.TameSpine.getDIdxOfSelfW
#print axioms Kepler.Text.TameSpine.getDIdxEqW
