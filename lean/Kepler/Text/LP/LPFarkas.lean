/-
  Kepler/Text/LP/LPFarkas — Farkas checker 内核下沉件（DEF-FIX，2026-10-12）。

  内核下沉件，源 = LPSchemaFarkas.lean §1-§2（C1b 车道落地，2026-10-12），
  按章程 docs/projects/lp-infeas-deffix.md §3 逐字搬运（闸 DEF-FIX）：
  内核五件 `LpFarkasCore`/`coreColSum`/`coreRhsSum`/`coreShape`/`farkasCheck`
  + soundness 引理族（`coreColSum_cast`/`coreRhsSum_cast`/`farkas_combo_eval`/
  `farkasCheck_sound`/`decimal_scale_le_iff`/`farkasCheck_scaled_sound`）
  + `getD_cons_zero'`/`getD_cons_succ'` 两 private 备件，正文零改动；
  全名（namespace Kepler.Text.LP）逐字节不变，下游消费者零感知。
  仅依赖 Mathlib 基础、零 Kepler 依赖。

  下沉原因：LPCert ← LPSchema ← LPSchemaFarkas 的 import 链方向使冻结陈述
  文件 LPCert 不可见原内核（其原在链上游 LPSchemaFarkas），循环 import
  禁止；本模块位于链底，LPCert 与 LPSchemaFarkas 都可安全引用
  （LPCert :73 定义体换 `∃ c : LpFarkasCore, farkasCheck c = true` 即章程
  §3.2，2026-10-12 DEF-FIX 已落地）。依赖 `LpPrecision`（LPSchema 侧类型）
  的两件（`LpPrecision.toNat_pos`/`farkasCheck_scaled_soundP`）不随迁，
  留在 LPSchemaFarkas 经本模块引用内核。

  语义定形（HOL 对账：formal_lp/prove_flyspeck_lp.hl:287-348 infeasible
  支）、设计取舍与实测记录的所有权文档在 LPSchemaFarkas.lean 模块头。
-/
import Mathlib.Tactic

namespace Kepler.Text.LP

/-! ## §1 内核数据载体与 checker（四步路径 ①） -/

/-- **Farkas 证书核**：解析后的缩放整数行系统 + 非负乘子（语义见模块头
「语义定形」；行 = constraints ∪ bounds ∪ targets，列 = 展开侧平坦
变量编号，`nvars` 为列数）。

不变式（checker 合取项）：三表平行（rows/rhs/mults 等长）+ 每行长
= nvars + 每列加权和为零 + rhs 加权和为负。 -/
structure LpFarkasCore where
  /-- 变量数（列数） -/
  nvars : Nat
  /-- 系数行（10^p 缩放整系数；每行长 = nvars） -/
  rows : List (List Int)
  /-- 右端项（10^p 缩放整数值） -/
  rhs : List Int
  /-- Farkas 乘子（非负由类型承担，HOL num 乘子直译） -/
  mults : List Nat

/-- 列和 `∑_j mⱼ · A[j][i]`（越界读 0；结构递归，内核可求值）。 -/
def coreColSum : List (List Int) → List Nat → Nat → Int
  | [], [], _ => 0
  | [], _ :: _, _ => 0
  | _ :: _, [], _ => 0
  | r :: rs, m :: ms, i => r.getD i 0 * (m : Int) + coreColSum rs ms i

/-- rhs 加权和 `∑_j mⱼ · bⱼ`（越界读 0）。 -/
def coreRhsSum : List Int → List Nat → Int
  | [], [] => 0
  | [], _ :: _ => 0
  | _ :: _, [] => 0
  | b :: bs, m :: ms => b * (m : Int) + coreRhsSum bs ms

/-- 形状检查：三表平行 + 每行长 = nvars。 -/
def coreShape (d : LpFarkasCore) : Bool :=
  d.rows.length == d.rhs.length && d.rhs.length == d.mults.length &&
    d.rows.all (fun r => r.length == d.nvars)

/-- **Farkas checker 内核**：形状良好 + 每列加权和为零（系数恒等式）+
rhs 加权和为负（`0 ≤ 负数` 矛盾形）。纯 Int 结构递归，decide 可求值。 -/
def farkasCheck (d : LpFarkasCore) : Bool :=
  coreShape d &&
    (List.range d.nvars).all (fun i => coreColSum d.rows d.mults i == 0) &&
    coreRhsSum d.rhs d.mults < 0

/-! ## §2 正确性（纯 ℤ/ℚ 线性代数；Finset 求和与 Σ 交换） -/

/-! ### List.getD 备件（自证，零 API 依赖） -/

private theorem getD_cons_zero' {α : Type u} (a : α) (l : List α) (d : α) :
    (a :: l).getD 0 d = a := rfl

private theorem getD_cons_succ' {α : Type u} (a : α) (l : List α) (d : α) (k : Nat) :
    (a :: l).getD (k + 1) d = l.getD k d := rfl

/-! ### 桥引理（递归内核 ↔ Finset 和，ℚ 口径） -/

/-- 列和桥：内核列和 = 非负乘子加权的列 Finset 和。 -/
theorem coreColSum_cast (rows : List (List Int)) (ms : List Nat) (h : rows.length = ms.length)
    (i : Nat) :
    (coreColSum rows ms i : ℚ) =
      ∑ j ∈ Finset.range rows.length, (ms.getD j 0 : ℚ) * ((rows.getD j []).getD i 0 : ℚ) := by
  induction rows generalizing ms with
  | nil =>
    cases ms with
    | nil => rfl
    | cons m ms => simp at h
  | cons r rs ih =>
    cases ms with
    | nil => simp at h
    | cons m ms =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      have hgoal : (coreColSum (r :: rs) (m :: ms) i : ℚ)
          = ((r.getD i 0 : ℚ) * (m : ℚ)) + (coreColSum rs ms i : ℚ) := by
        simp only [coreColSum]
        push_cast
        rfl
      rw [hgoal, ih ms h, List.length_cons, Finset.sum_range_succ']
      simp only [getD_cons_succ', getD_cons_zero']
      ring

/-- rhs 和桥：内核 rhs 和 = 非负乘子加权的 rhs Finset 和。 -/
theorem coreRhsSum_cast (b : List Int) (ms : List Nat) (h : b.length = ms.length) :
    (coreRhsSum b ms : ℚ) =
      ∑ j ∈ Finset.range b.length, (ms.getD j 0 : ℚ) * (b.getD j 0 : ℚ) := by
  induction b generalizing ms with
  | nil =>
    cases ms with
    | nil => rfl
    | cons m ms => simp at h
  | cons c cs ih =>
    cases ms with
    | nil => simp at h
    | cons m ms =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      have hgoal : (coreRhsSum (c :: cs) (m :: ms) : ℚ)
          = ((c : ℚ) * (m : ℚ)) + (coreRhsSum cs ms : ℚ) := by
        simp only [coreRhsSum]
        push_cast
        rfl
      rw [hgoal, ih ms h, List.length_cons, Finset.sum_range_succ']
      simp only [getD_cons_succ', getD_cons_zero']
      ring

/-! ### 主组合定理 -/

/-- **Farkas 组合求值**：形状良好的系统（三表平行）在任何 ℚ 赋值与
可行假设（每行 ≤ rhs）下，非负乘子组合的行和 = 加权列和的点积
≤ 加权 rhs 和。这是 HOL `add_step'` 链（乘子缩放 + 逐条相加 + 逐变量
对消）的整体语义。 -/
theorem farkas_combo_eval (d : LpFarkasCore)
    (hlen : d.rows.length = d.rhs.length ∧ d.rhs.length = d.mults.length)
    (w : Nat → ℚ)
    (hsat : ∀ j < d.rows.length,
      (∑ i ∈ Finset.range d.nvars, ((d.rows.getD j []).getD i 0 : ℚ) * w i)
        ≤ ((d.rhs.getD j 0 : ℚ))) :
    (∑ i ∈ Finset.range d.nvars, (coreColSum d.rows d.mults i : ℚ) * w i)
      ≤ (coreRhsSum d.rhs d.mults : ℚ) := by
  have key : ∀ j ∈ Finset.range d.rows.length,
      (d.mults.getD j 0 : ℚ) * (∑ i ∈ Finset.range d.nvars,
        ((d.rows.getD j []).getD i 0 : ℚ) * w i)
        ≤ (d.mults.getD j 0 : ℚ) * ((d.rhs.getD j 0 : ℚ)) := by
    intro j hj
    exact mul_le_mul_of_nonneg_left (hsat j (Finset.mem_range.mp hj)) (Nat.cast_nonneg _)
  have hsum : ∑ j ∈ Finset.range d.rows.length,
      (d.mults.getD j 0 : ℚ) * (∑ i ∈ Finset.range d.nvars,
        ((d.rows.getD j []).getD i 0 : ℚ) * w i)
      ≤ ∑ j ∈ Finset.range d.rows.length, (d.mults.getD j 0 : ℚ) * ((d.rhs.getD j 0 : ℚ)) :=
    Finset.sum_le_sum key
  have hsum2 : (∑ j ∈ Finset.range d.rows.length,
      (d.mults.getD j 0 : ℚ) * (∑ i ∈ Finset.range d.nvars,
        ((d.rows.getD j []).getD i 0 : ℚ) * w i))
      ≤ (∑ j ∈ Finset.range d.rhs.length, (d.mults.getD j 0 : ℚ) * ((d.rhs.getD j 0 : ℚ))) := by
    rw [← hlen.1]
    exact hsum
  have hlhs : ∑ j ∈ Finset.range d.rows.length,
      (d.mults.getD j 0 : ℚ) * (∑ i ∈ Finset.range d.nvars,
        ((d.rows.getD j []).getD i 0 : ℚ) * w i)
      = ∑ i ∈ Finset.range d.nvars, (coreColSum d.rows d.mults i : ℚ) * w i := by
    have step1 : ∑ j ∈ Finset.range d.rows.length,
        (d.mults.getD j 0 : ℚ) * (∑ i ∈ Finset.range d.nvars,
          ((d.rows.getD j []).getD i 0 : ℚ) * w i)
        = ∑ j ∈ Finset.range d.rows.length, ∑ i ∈ Finset.range d.nvars,
          (d.mults.getD j 0 : ℚ) * (((d.rows.getD j []).getD i 0 : ℚ) * w i) :=
      Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
    have step2 : ∑ j ∈ Finset.range d.rows.length, ∑ i ∈ Finset.range d.nvars,
        (d.mults.getD j 0 : ℚ) * (((d.rows.getD j []).getD i 0 : ℚ) * w i)
        = ∑ i ∈ Finset.range d.nvars, ∑ j ∈ Finset.range d.rows.length,
          (d.mults.getD j 0 : ℚ) * (((d.rows.getD j []).getD i 0 : ℚ) * w i) :=
      Finset.sum_comm
    refine step1.trans (step2.trans ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    have step4 : (∑ j ∈ Finset.range d.rows.length,
        (d.mults.getD j 0 : ℚ) * ((d.rows.getD j []).getD i 0 : ℚ)) * w i
        = ∑ j ∈ Finset.range d.rows.length,
          ((d.mults.getD j 0 : ℚ) * ((d.rows.getD j []).getD i 0 : ℚ)) * w i :=
      Finset.sum_mul _ _ _
    calc ∑ j ∈ Finset.range d.rows.length,
        (d.mults.getD j 0 : ℚ) * (((d.rows.getD j []).getD i 0 : ℚ) * w i)
        = ∑ j ∈ Finset.range d.rows.length,
          ((d.mults.getD j 0 : ℚ) * ((d.rows.getD j []).getD i 0 : ℚ)) * w i :=
          Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
      _ = (∑ j ∈ Finset.range d.rows.length,
          (d.mults.getD j 0 : ℚ) * ((d.rows.getD j []).getD i 0 : ℚ)) * w i := step4.symm
      _ = (coreColSum d.rows d.mults i : ℚ) * w i := by
          rw [coreColSum_cast d.rows d.mults (hlen.1.trans hlen.2) i]
  rw [← hlhs, coreRhsSum_cast d.rhs d.mults hlen.2]
  exact hsum2

/-- **Farkas 正确性（主定理）**：checker 通过 ⟹ 该行系统在任何 ℚ 赋值下
不可满足（任一满足全行的赋值导出 `0 ≤ Σ mⱼ bⱼ < 0` 矛盾）。 -/
theorem farkasCheck_sound (d : LpFarkasCore) (h : farkasCheck d = true) (w : Nat → ℚ) :
    ¬ ∀ j < d.rows.length,
      (∑ i ∈ Finset.range d.nvars, ((d.rows.getD j []).getD i 0 : ℚ) * w i)
        ≤ ((d.rhs.getD j 0 : ℚ)) := by
  intro hsat
  have h1 : (d.rows.length == d.rhs.length) = true ∧ (d.rhs.length == d.mults.length) = true ∧
      (d.rows.all (fun r => r.length == d.nvars)) = true ∧
      ((List.range d.nvars).all (fun i => coreColSum d.rows d.mults i == 0) = true) ∧
      coreRhsSum d.rhs d.mults < 0 := by
    simp only [farkasCheck, coreShape, Bool.and_assoc, Bool.and_eq_true_iff,
      decide_eq_true_eq] at h
    exact h
  obtain ⟨hab, hbm, -, hall, hrhs⟩ := h1
  have hlen : d.rows.length = d.rhs.length ∧ d.rhs.length = d.mults.length :=
    ⟨beq_iff_eq.mp hab, beq_iff_eq.mp hbm⟩
  have hcolQ : ∀ i < d.nvars, (coreColSum d.rows d.mults i : ℚ) = 0 := by
    intro i hi
    have hi' := List.all_eq_true.mp hall i (List.mem_range.mpr hi)
    rw [beq_iff_eq] at hi'
    rw [hi', Int.cast_zero]
  have hrhsQ : (coreRhsSum d.rhs d.mults : ℚ) < 0 := Int.cast_lt.mpr hrhs
  have hcombo := farkas_combo_eval d hlen w hsat
  have hzero : (∑ i ∈ Finset.range d.nvars, (coreColSum d.rows d.mults i : ℚ) * w i) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hcolQ i (Finset.mem_range.mp hi), zero_mul]
  rw [hzero] at hcombo
  exact absurd hrhsQ (not_lt.mpr hcombo)

/-! ### 10^p 缩放的精确性论证 -/

/-- **缩放精确性**：DECIMAL 十进制系数系统（系数 `a/10^p`）与缩放整数
系统（系数 `a`）逐不等式等价——两边同乘 `10^p > 0` 保序。HOL 侧对应
`mul_step` 的整体 `precision_constant` 缩放（prove_flyspeck_lp.hl:331）。 -/
theorem decimal_scale_le_iff {p : Nat} {n : Nat} (A : Nat → ℚ) (b : ℚ) (w : Nat → ℚ) :
    (∑ i ∈ Finset.range n, (A i / (10 : ℚ) ^ p) * w i) ≤ b / (10 : ℚ) ^ p
      ↔ (∑ i ∈ Finset.range n, A i * w i) ≤ b := by
  have hp : (0 : ℚ) < (10 : ℚ) ^ p := by positivity
  have hsumdiv : (∑ i ∈ Finset.range n, (A i / (10 : ℚ) ^ p) * w i)
      = (∑ i ∈ Finset.range n, A i * w i) / (10 : ℚ) ^ p := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => div_mul_eq_mul_div _ _ _
  constructor
  · intro h
    rw [hsumdiv, div_le_iff₀ hp] at h
    field_simp at h
    exact h
  · intro h
    rw [hsumdiv, div_le_iff₀ hp]
    field_simp
    exact h

/-- 缩放不可行性推论：整数 checker 通过 ⟹ 10^p 十进制缩放系统同样
不可行（与 LpPrecision p3..p7 的缩放口径衔接见 `farkasCheck_scaled_soundP`）。 -/
theorem farkasCheck_scaled_sound (d : LpFarkasCore) (h : farkasCheck d = true) (p : Nat)
    (w : Nat → ℚ) :
    ¬ ∀ j < d.rows.length,
      (∑ i ∈ Finset.range d.nvars, ((d.rows.getD j []).getD i 0 : ℚ) / (10 : ℚ) ^ p * w i)
        ≤ ((d.rhs.getD j 0 : ℚ) / (10 : ℚ) ^ p) :=
  fun hsat =>
    farkasCheck_sound d h w fun j hj => (decimal_scale_le_iff _ _ _).mp (hsat j hj)

end Kepler.Text.LP
