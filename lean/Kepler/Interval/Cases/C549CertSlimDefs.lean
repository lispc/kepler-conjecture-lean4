/-
  549 加速项目 — cert 层瘦身工位：**裸区间（`evalIParams`）定号证书路线**。

  ## 背景（docs/549-lane-log.md 十更/十一更）

  mono 折叠链的证书层损耗 35.3%，归因：guard 证书叶（`safeIteNeg` 路线）
  的 TM 下界（`checkPosTMHull (.neg guard)`）被 **√S 子模型的 Taylor 余项**
  吃掉——29/178 样本叶 NEG，而其精确 guard 裕量（−sup g）最薄仍有 0.26
  （贴面距离并不小；失败与 TM 余项同量级，与叶宽无关）。

  ## 本模块内容（只走已证 sound 路径）

  `evalIParams` 的 soundness `evalIParams_mem`（CertTM.lean，标准三公理）：
  求值成功 ⇒ 返回区间逐点包含真值。据此组装三个 Bool 级定号检查器与
  `DerivSafeOn` 接口的 discharge 引理（与 `safeDivPos/safeIteNeg/...` 同型）：

  - `checkNegI`：上端 < 0 ⇒ 逐点负（guard then 支 / div neg 形）；
  - `checkPosI`：下端 > 0 ⇒ 逐点正（div pos 形 / sqrt 底 / guard else 支）；
  - `checkNeI`：下端 > 0 ∨ 上端 < 0 ⇒ 逐点非零（div abs 形）。

  证书叶发射为 `check*I box form params = true` 的内核 `decide`（裸区间
  求值：多项式段精确 dyadic 区间算术，`sqrt` 经烘焙的精确下取整 mantissa
  证书），替代 TM 下界叶。零新增公理、零 `native_decide`。

  本模块为评估模块（C549CertSlim* 系列），不进入 C549Mono 主链。
-/
import Kepler.Interval.Cases.C549Mono

namespace Kepler.Interval

/-! ## 裸区间定号检查器 -/

/-- 负性检查器：`evalIParams` 求值成功且区间上端 < 0。 -/
def checkNegI {n : ℕ} (e : IExpr n) (box : Fin n → DInterval) (ps : TMParams) : Bool :=
  match evalIParams box e ps with
  | some (I, _) => I.hi.isNeg
  | none => false

/-- 正性检查器：`evalIParams` 求值成功且区间下端 > 0。 -/
def checkPosI {n : ℕ} (e : IExpr n) (box : Fin n → DInterval) (ps : TMParams) : Bool :=
  match evalIParams box e ps with
  | some (I, _) => I.lo.isPos
  | none => false

/-- 非零检查器：`evalIParams` 求值成功且区间与 0 分离（下端 > 0 ∨ 上端 < 0）。 -/
def checkNeI {n : ℕ} (e : IExpr n) (box : Fin n → DInterval) (ps : TMParams) : Bool :=
  match evalIParams box e ps with
  | some (I, _) => I.lo.isPos || I.hi.isNeg
  | none => false

/-! ## Soundness（evalIParams_mem + 端点符号引理组装；标准三公理） -/

/-- `checkNegI` 的 soundness：证书区间上端 < 0 ⇒ 表达式盒上逐点负。 -/
theorem checkNegI_sound {n : ℕ} {box : Fin n → DInterval} {e : IExpr n}
    {ps : TMParams} (h : checkNegI e box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → e.evalReal ρ < 0 := by
  intro ρ hρ
  unfold checkNegI at h
  split at h
  · rename_i I ps' hE
    obtain ⟨_, hhi⟩ := evalIParams_mem hρ e ps ps' I hE
    exact lt_of_le_of_lt hhi ((Dyadic.isNeg_iff I.hi).mp h)
  · exact absurd h (by simp)

/-- `checkPosI` 的 soundness：证书区间下端 > 0 ⇒ 表达式盒上逐点正。 -/
theorem checkPosI_sound {n : ℕ} {box : Fin n → DInterval} {e : IExpr n}
    {ps : TMParams} (h : checkPosI e box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → 0 < e.evalReal ρ := by
  intro ρ hρ
  unfold checkPosI at h
  split at h
  · rename_i I ps' hE
    obtain ⟨hlo, _⟩ := evalIParams_mem hρ e ps ps' I hE
    exact lt_of_lt_of_le ((Dyadic.isPos_iff I.lo).mp h) hlo
  · exact absurd h (by simp)

/-- `checkNeI` 的 soundness：证书区间与 0 分离 ⇒ 表达式盒上逐点非零。 -/
theorem checkNeI_sound {n : ℕ} {box : Fin n → DInterval} {e : IExpr n}
    {ps : TMParams} (h : checkNeI e box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → e.evalReal ρ ≠ 0 := by
  intro ρ hρ
  unfold checkNeI at h
  split at h
  · rename_i I ps' hE
    obtain ⟨hlo, hhi⟩ := evalIParams_mem hρ e ps ps' I hE
    cases hp : I.lo.isPos with
    | true => exact ne_of_gt (lt_of_lt_of_le ((Dyadic.isPos_iff I.lo).mp hp) hlo)
    | false =>
        have hn : I.hi.isNeg = true := by simpa [hp] using h
        exact ne_of_lt (lt_of_le_of_lt hhi ((Dyadic.isNeg_iff I.hi).mp hn))
  · exact absurd h (by simp)

/-! ## DerivSafeOn 接口 discharge 引理（与 safeDivPos 族逐条同型） -/

/-- ite guard 盒上严格负（then 支选中；裸区间路线——证书叶走 neg 形文本
`(.neg c)` 的正性，与 `safeIteNeg` 的 `checkPosTMHull (IExpr.neg c)` 同构）。 -/
theorem safeIteNegI {n : ℕ} {c : IExpr n} {box : Fin n → DInterval} {ps : TMParams}
    (h : checkPosI (IExpr.neg c) box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → c.evalReal ρ < 0 := by
  intro ρ hρ
  have h2 : 0 < (IExpr.neg c).evalReal ρ := checkPosI_sound h ρ hρ
  simp only [IExpr.evalReal] at h2
  linarith

/-- ite guard 盒上 ≥0（else 支选中；裸区间路线）。 -/
theorem safeIteNNI {n : ℕ} {c : IExpr n} {box : Fin n → DInterval} {ps : TMParams}
    (h : checkPosI c box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → 0 ≤ c.evalReal ρ :=
  fun ρ hρ => le_of_lt (checkPosI_sound h ρ hρ)

/-- div 分母盒上严格正 ⇒ 非零（pos 形；裸区间路线）。 -/
theorem safeDivPosI {n : ℕ} {b : IExpr n} {box : Fin n → DInterval} {ps : TMParams}
    (h : checkPosI b box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → b.evalReal ρ ≠ 0 :=
  fun ρ hρ => ne_of_gt (checkPosI_sound h ρ hρ)

/-- div 分母盒上严格负 ⇒ 非零（neg 形证书叶 `(.neg b)` 的正性；裸区间路线）。 -/
theorem safeDivNegI {n : ℕ} {b : IExpr n} {box : Fin n → DInterval} {ps : TMParams}
    (h : checkPosI (IExpr.neg b) box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → b.evalReal ρ ≠ 0 := by
  intro ρ hρ
  have h2 : 0 < (IExpr.neg b).evalReal ρ := checkPosI_sound h ρ hρ
  simp only [IExpr.evalReal] at h2
  linarith

/-- div 分母盒上与 0 分离（abs 形证书叶 `(.abs b)` 的正性；裸区间路线）. -/
theorem safeDivAbsI {n : ℕ} {b : IExpr n} {box : Fin n → DInterval} {ps : TMParams}
    (h : checkPosI (IExpr.abs b) box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → b.evalReal ρ ≠ 0 := by
  intro ρ hρ
  have h2 : 0 < (IExpr.abs b).evalReal ρ := checkPosI_sound h ρ hρ
  simp only [IExpr.evalReal] at h2
  intro h0
  rw [h0] at h2
  simp at h2

/-- sqrt 底盒上严格正（裸区间路线）。 -/
theorem safeSqrtPosI {n : ℕ} {a : IExpr n} {box : Fin n → DInterval} {ps : TMParams}
    (h : checkPosI a box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → 0 < a.evalReal ρ := checkPosI_sound h

/-! ## 补充 API：neg/abs 形也可直接在裸表达式上定号（非发射侧所需） -/

/-- 负形变体：`checkNegI b`（b 的区间上端 < 0）⇒ 逐点负。 -/
theorem safeNegI {n : ℕ} {b : IExpr n} {box : Fin n → DInterval} {ps : TMParams}
    (h : checkNegI b box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → b.evalReal ρ < 0 := checkNegI_sound h

/-- 非零形变体：`checkNeI b`（区间与 0 分离）⇒ 逐点非零。 -/
theorem safeNeI {n : ℕ} {b : IExpr n} {box : Fin n → DInterval} {ps : TMParams}
    (h : checkNeI b box ps = true) :
    ∀ ρ : Fin n → ℝ, boxMem box ρ → b.evalReal ρ ≠ 0 := checkNeI_sound h

/-! ## 微型端到端（裸区间证书叶 → DerivSafeOnM.iteNeg） -/

/-- box `[2, 5/2]`。 -/
def miniBoxI : Fin 1 → DInterval := fun _ => ⟨⟨2, 0⟩, ⟨5, -1⟩⟩

/-- guard `3/2 − x` 在 `[2, 5/2]` 上区间为 `[-1, -1/2]`：neg 形证书叶
`x − 3/2` 区间 `[1/2, 1]` 定号正 ⇒ `ite (3/2 − x, 2x, x)` 的 then 支可导安全。 -/
theorem miniIteNegI :
    DerivSafeOn miniBoxI
      (.ite (.sub (.const ⟨3, -1⟩) (.var 0)) (.mul (.var 0) (.const ⟨2, 0⟩))
        (.var 0)) := by
  refine DerivSafeOnM.iteNeg
    (DerivSafeOnM.mul (DerivSafeOnM.var (0 : Fin 1) (m := true))
      (DerivSafeOnM.const ⟨2, 0⟩ (m := true))) ?_
  intro ρ hρ
  have hc : checkPosI (IExpr.neg (.sub (.const ⟨3, -1⟩) (.var 0))) miniBoxI
      TMParams.empty = true := by decide
  exact safeIteNegI hc ρ hρ

#print axioms checkNegI_sound
#print axioms checkPosI_sound
#print axioms checkNeI_sound
#print axioms safeIteNegI
#print axioms safeDivNegI
#print axioms safeDivAbsI
#print axioms miniIteNegI

end Kepler.Interval
