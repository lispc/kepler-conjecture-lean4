/-
  549 加速项目 — M1 核心：**facePos 单调性折叠规则**（Result_mono 的 Lean 落地）。

  ## 数学内容

  原版 Flyspeck 的主折叠杠杆：`∂ⱼf` 在盒上定号 ⇒ 下界在某一面取得，验
  n−1 维面即可。本模块给出该折叠的完整 Lean 语义链（零新增公理）：

  1. `derivIExpr`：`IExpr` 的符号偏导（纯语法构造子变换：`±×÷√atan(sin/cos/ln)`
     链式/商法则；`ite` 微分 guard 定号选中的 then 支——soundness 由
     `DerivSafeOn.iteNeg` 消费；`abs` 返回零桩——`abs` 无 `DerivSafeOn` 构造子，
     桩永不被消费）。
  2. `DerivSafeOn box e`：可导性安全谓词（div 分母盒上非零、sqrt 底盒上为正、
     ln 底盒上非零、ite guard 盒上严格负）。对偶数链规则
     `derivIExpr_hasDerivWithinAt`：对 e 归纳，`HasDerivWithinAt` 版（uIcc 闭线段，
     端点安全——ite 经 within-集 eventual congruence）。
  3. `faceBoxLo`/`faceBoxHi`：j 坐标钉在 lo/hi 端点的退化面盒；
     `facePosLo`/`facePosHi`：坐标线段 MVT（`exists_hasDerivAt_eq_slope`）——
     `∂ⱼf > 0` ⇒ `f(ρ) ≥ f(ρ[j←lo])`，故面正 ⇒ 盒正（`∂ⱼf < 0` 对称取 hi 面）。
  4. `checkPosFaceLo`/`checkPosFaceHi`：**mono 折叠检查器** =
     `checkPosTMHull ±∂ⱼf box`（导数正性叶，全盒）`&&` `checkPosTMHull e faceBox`
     （面叶，n−1 维）——两叶 PASS 即折叠掉原全盒叶（soundness：
     `checkPosFaceLo_sound`/`checkPosFaceHi_sound`）。

  叶数折叠预期：全 6 坐标均匀二叉加细下 2^(6k) → 2^(5k)，即
  叶数^(5/6)（212,798 → ≈2.8 万，保守）。

  M2 待办（本模块不声称）：对真实 549 表达式发射 `DerivSafeOn` 证明项
  （per-div/per-sqrt 定号证书叶 + ite guard 定号证书链）、ite else 支支持。

  无 `sorry`、无 `native_decide`、无新增 axiom。
-/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval

/-! ## 符号偏导 `derivIExpr`（语法层） -/

/-- `IExpr` 对坐标 `j` 的符号偏导：纯语法构造子变换（链式/商法则）。
`ite` 微分 then 支（guard 定号负时 sound——`DerivSafeOn.iteNeg`）；
`abs` 返回零桩（`abs` 不可导，无 `DerivSafeOn` 构造子，桩永不被消费）；
生成的 `div` 粒度参数只影响区间精度，不影响语义正确性。 -/
def derivIExpr {n : ℕ} (e : IExpr n) (j : Fin n) : IExpr n :=
  match e with
  | .const _ => .const ⟨0, 0⟩
  | .var i => if i = j then .const ⟨1, 0⟩ else .const ⟨0, 0⟩
  | .neg a => .neg (derivIExpr a j)
  | .abs _ => .const ⟨0, 0⟩
  | .ite _ t _ => derivIExpr t j
  | .add a b => .add (derivIExpr a j) (derivIExpr b j)
  | .sub a b => .sub (derivIExpr a j) (derivIExpr b j)
  | .mul a b => .add (.mul (derivIExpr a j) b) (.mul a (derivIExpr b j))
  | .div a b out =>
      .div (.sub (.mul (derivIExpr a j) b) (.mul a (derivIExpr b j))) (.mul b b) out
  | .sqrt a s₁ s₂ =>
      .div (derivIExpr a j) (.add (.sqrt a s₁ s₂) (.sqrt a s₁ s₂)) 0
  | .trans k a N out =>
      match k with
      | .sinK => .mul (.trans .cosK a N out) (derivIExpr a j)
      | .cosK => .neg (.mul (.trans .sinK a N out) (derivIExpr a j))
      | .arctanK => .div (derivIExpr a j) (.add (.const ⟨1, 0⟩) (.mul a a)) 0
      | .lnK => .div (derivIExpr a j) a 0

/-! ## 可导性安全谓词 `DerivSafeOn` -/

/-- `e` 在 `box` 上对每个坐标可导、且导数 = `(derivIExpr e j).evalReal`（对每个
`j`）所需的逐节点安全条件：div 分母盒上非零、sqrt 底盒上严格正、ln 底盒上
非零、ite guard 盒上严格负（then 支选中；else 支为 M2 扩展）。 -/
inductive DerivSafeOn {n : ℕ} (box : Fin n → DInterval) : IExpr n → Prop
  | const (d : Dyadic) : DerivSafeOn box (.const d)
  | var (i : Fin n) : DerivSafeOn box (.var i)
  | neg {e : IExpr n} (h : DerivSafeOn box e) : DerivSafeOn box (.neg e)
  | add {e₁ e₂ : IExpr n} (h₁ : DerivSafeOn box e₁) (h₂ : DerivSafeOn box e₂) :
      DerivSafeOn box (.add e₁ e₂)
  | sub {e₁ e₂ : IExpr n} (h₁ : DerivSafeOn box e₁) (h₂ : DerivSafeOn box e₂) :
      DerivSafeOn box (.sub e₁ e₂)
  | mul {e₁ e₂ : IExpr n} (h₁ : DerivSafeOn box e₁) (h₂ : DerivSafeOn box e₂) :
      DerivSafeOn box (.mul e₁ e₂)
  | div {e₁ e₂ : IExpr n} {out : Int} (h₁ : DerivSafeOn box e₁)
      (h₂ : DerivSafeOn box e₂) (hz : ∀ ρ : Fin n → ℝ, boxMem box ρ → e₂.evalReal ρ ≠ 0) :
      DerivSafeOn box (.div e₁ e₂ out)
  | sqrt {e : IExpr n} {s₁ s₂ : Int} (h : DerivSafeOn box e)
      (hp : ∀ ρ : Fin n → ℝ, boxMem box ρ → 0 < e.evalReal ρ) :
      DerivSafeOn box (.sqrt e s₁ s₂)
  | trans {k : TKind} {e : IExpr n} {N : ℕ} {out : Int} (h : DerivSafeOn box e)
      (hk : k = .sinK ∨ k = .cosK ∨ k = .arctanK) :
      DerivSafeOn box (.trans k e N out)
  | transLn {e : IExpr n} {N : ℕ} {out : Int} (h : DerivSafeOn box e)
      (hz : ∀ ρ : Fin n → ℝ, boxMem box ρ → e.evalReal ρ ≠ 0) :
      DerivSafeOn box (.trans .lnK e N out)
  | iteNeg {c t e : IExpr n} (h : DerivSafeOn box t)
      (hneg : ∀ ρ : Fin n → ℝ, boxMem box ρ → c.evalReal ρ < 0) :
      DerivSafeOn box (.ite c t e)

/-! ## 面盒 -/

/-- lo 面盒：j 坐标钉在盒的 lo 端点（n−1 维面）。 -/
def faceBoxLo {n : ℕ} (box : Fin n → DInterval) (j : Fin n) : Fin n → DInterval :=
  Function.update box j ⟨(box j).lo, (box j).lo⟩

/-- hi 面盒：j 坐标钉在盒的 hi 端点。 -/
def faceBoxHi {n : ℕ} (box : Fin n → DInterval) (j : Fin n) : Fin n → DInterval :=
  Function.update box j ⟨(box j).hi, (box j).hi⟩

/-! ## 坐标线段与良域性 -/

/-- 坐标 `j` 线段：`ρ` 把第 `j` 个坐标搬到 `x`。 -/
def updR {n : ℕ} (ρ : Fin n → ℝ) (j : Fin n) (x : ℝ) : Fin n → ℝ :=
  Function.update ρ j x

theorem updR_self {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} : updR ρ j (ρ j) = ρ :=
  Function.update_eq_self j ρ

theorem boxMem_updR {n : ℕ} {box : Fin n → DInterval} {j : Fin n} {ρ : Fin n → ℝ}
    (hρ : boxMem box ρ) {x : ℝ} (hx : (box j).lo.toReal ≤ x ∧ x ≤ (box j).hi.toReal) :
    boxMem box (updR ρ j x) := by
  intro i
  by_cases h : i = j
  · rw [h]
    show (box j).mem (Function.update ρ j x j)
    rw [Function.update_self]
    exact hx
  · show (box i).mem (Function.update ρ j x i)
    rw [Function.update_of_ne h]
    exact hρ i

theorem boxMem_faceBoxLo {n : ℕ} {box : Fin n → DInterval} {j : Fin n}
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) :
    boxMem (faceBoxLo box j) (updR ρ j (box j).lo.toReal) := by
  intro i
  by_cases h : i = j
  · rw [h, faceBoxLo, updR, Function.update_self, Function.update_self]
    exact ⟨le_rfl, le_rfl⟩
  · rw [faceBoxLo, updR, Function.update_of_ne h, Function.update_of_ne h]
    exact hρ i

theorem boxMem_faceBoxHi {n : ℕ} {box : Fin n → DInterval} {j : Fin n}
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) :
    boxMem (faceBoxHi box j) (updR ρ j (box j).hi.toReal) := by
  intro i
  by_cases h : i = j
  · rw [h, faceBoxHi, updR, Function.update_self, Function.update_self]
    exact ⟨le_rfl, le_rfl⟩
  · rw [faceBoxHi, updR, Function.update_of_ne h, Function.update_of_ne h]
    exact hρ i

/-! ## 链式法则（对 `DerivSafeOn` 归纳） -/

/-- **导数正确性**（链式法则）：盒上线段上，`e.evalReal ∘ 线段` 在
`uIcc lo hi` 内每点可导，导数 = `(derivIExpr e j).evalReal ∘ 线段`。
用 `HasDerivWithinAt`（闭线段）表述：端点安全（ite 经 within-集
eventual congruence；非 ite 节点的安全条件逐点成立）。 -/
theorem derivIExpr_hasDerivWithinAt {n : ℕ} {box : Fin n → DInterval} {j : Fin n}
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) :
    ∀ {e : IExpr n}, DerivSafeOn box e → ∀ {x : ℝ}, (box j).lo.toReal ≤ x →
      x ≤ (box j).hi.toReal →
      HasDerivWithinAt (fun x' => e.evalReal (updR ρ j x'))
        ((derivIExpr e j).evalReal (updR ρ j x))
        (Set.uIcc (box j).lo.toReal (box j).hi.toReal) x := by
  have hlohi : (box j).lo.toReal ≤ (box j).hi.toReal := (hρ j).1.trans (hρ j).2
  have hlohi' : Set.uIcc (box j).lo.toReal (box j).hi.toReal
      = Set.Icc (box j).lo.toReal (box j).hi.toReal := Set.uIcc_of_le hlohi
  intro e hD
  induction hD with
  | const d =>
      intro x _ _
      simp only [derivIExpr, IExpr.evalReal, Dyadic.toReal_zero]
      exact hasDerivWithinAt_const x _ (d.toReal)
  | var i =>
      intro x _ _
      by_cases h : i = j
      · have hfun : (fun x' => (IExpr.var i).evalReal (updR ρ j x'))
            = (fun x' : ℝ => x') := by
          funext x'
          simp only [IExpr.evalReal, updR]
          rw [h, Function.update_self]
        have hdv : (derivIExpr (IExpr.var i) j).evalReal (updR ρ j x) = 1 := by
          simp only [derivIExpr, if_pos h, IExpr.evalReal, Dyadic.toReal_one]
        rw [hfun, hdv]
        exact hasDerivWithinAt_id x _
      · have hfun : (fun x' => (IExpr.var i).evalReal (updR ρ j x'))
            = (fun _ : ℝ => ρ i) := by
          funext x'
          simp only [IExpr.evalReal, updR]
          rw [Function.update_of_ne h]
        have hdv : (derivIExpr (IExpr.var i) j).evalReal (updR ρ j x) = 0 := by
          simp only [derivIExpr, if_neg h, IExpr.evalReal, Dyadic.toReal_zero]
        rw [hfun, hdv]
        exact hasDerivWithinAt_const x _ (ρ i)
  | neg h ih =>
      intro x hx1 hx2
      simp only [derivIExpr, IExpr.evalReal]
      exact (ih hx1 hx2).neg.congr_deriv (by simp)
  | add h₁ h₂ ih₁ ih₂ =>
      intro x hx1 hx2
      simp only [derivIExpr, IExpr.evalReal]
      exact (ih₁ hx1 hx2).add (ih₂ hx1 hx2)
  | sub h₁ h₂ ih₁ ih₂ =>
      intro x hx1 hx2
      simp only [derivIExpr, IExpr.evalReal]
      exact (ih₁ hx1 hx2).sub (ih₂ hx1 hx2)
  | mul h₁ h₂ ih₁ ih₂ =>
      intro x hx1 hx2
      simp only [derivIExpr, IExpr.evalReal]
      exact (ih₁ hx1 hx2).mul (ih₂ hx1 hx2)
  | div h₁ h₂ hz ih₁ ih₂ =>
      intro x hx1 hx2
      have hσ := boxMem_updR hρ ⟨hx1, hx2⟩
      have hne := hz (updR ρ j x) hσ
      simp only [derivIExpr, IExpr.evalReal]
      exact ((ih₁ hx1 hx2).div (ih₂ hx1 hx2) hne).congr_deriv (by ring)
  | sqrt h hp ih =>
      intro x hx1 hx2
      have hσ := boxMem_updR hρ ⟨hx1, hx2⟩
      have hpos := hp (updR ρ j x) hσ
      simp only [derivIExpr, IExpr.evalReal]
      refine ((ih hx1 hx2).sqrt (ne_of_gt hpos)).congr_deriv ?_
      rw [two_mul]
  | trans h hk ih =>
      intro x hx1 hx2
      rcases hk with rfl | rfl | rfl
      · simp only [derivIExpr, IExpr.evalReal, transReal]
        refine ((Real.hasDerivAt_sin _).comp_hasDerivWithinAt x (ih hx1 hx2)).congr_deriv ?_
        ring
      · simp only [derivIExpr, IExpr.evalReal, transReal]
        refine ((Real.hasDerivAt_cos _).comp_hasDerivWithinAt x (ih hx1 hx2)).congr_deriv ?_
        ring
      · simp only [derivIExpr, IExpr.evalReal, transReal, Dyadic.toReal_one]
        refine ((Real.hasDerivAt_arctan _).comp_hasDerivWithinAt x (ih hx1 hx2)).congr_deriv ?_
        ring
  | transLn h hz ih =>
      intro x hx1 hx2
      have hσ := boxMem_updR hρ ⟨hx1, hx2⟩
      have hne := hz (updR ρ j x) hσ
      simp only [derivIExpr, IExpr.evalReal, transReal]
      refine ((Real.hasDerivAt_log hne).comp_hasDerivWithinAt x (ih hx1 hx2)).congr_deriv ?_
      ring
  | iteNeg h hneg ih =>
      intro x hx1 hx2
      have hσx := boxMem_updR hρ ⟨hx1, hx2⟩
      refine HasDerivWithinAt.congr (ih hx1 hx2) ?_ ?_
      · intro y hy
        rw [hlohi'] at hy
        have hσ := boxMem_updR hρ hy
        simp only [IExpr.evalReal]
        rw [if_pos (hneg _ hσ)]
      · simp only [IExpr.evalReal]
        rw [if_pos (hneg _ hσx)]

/-! ## facePos 折叠引理（坐标线段 MVT） -/

/-- **facePos 核心引理（lo 面，`∂ⱼf > 0`）**：`f` 在盒上沿坐标 `j` 的线段
可导（`hmaster`，闭线段 within 形式）、导数 `d` 全盒严格正、`f` 在 lo 面盒
严格正 ⇒ `f` 全盒严格正。证明：MVT（`exists_hasDerivAt_eq_slope`）——
`f(ρ) − f(ρ[j←lo]) = (ρⱼ − lo)·d(线段上某点) > 0`。 -/
theorem facePosLo {n : ℕ} {box : Fin n → DInterval} {j : Fin n}
    {f d : (Fin n → ℝ) → ℝ}
    (hmaster : ∀ ρ : Fin n → ℝ, boxMem box ρ → ∀ x : ℝ, (box j).lo.toReal ≤ x →
      x ≤ (box j).hi.toReal →
      HasDerivWithinAt (fun x' => f (updR ρ j x')) (d (updR ρ j x))
        (Set.uIcc (box j).lo.toReal (box j).hi.toReal) x)
    (hdpos : ∀ ρ : Fin n → ℝ, boxMem box ρ → 0 < d ρ)
    (hface : ∀ ρ : Fin n → ℝ, boxMem (faceBoxLo box j) ρ → 0 < f ρ)
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) : 0 < f ρ := by
  have hlo : (box j).lo.toReal ≤ ρ j := (hρ j).1
  have hhi : ρ j ≤ (box j).hi.toReal := (hρ j).2
  have hlohi : Set.uIcc (box j).lo.toReal (box j).hi.toReal
      = Set.Icc (box j).lo.toReal (box j).hi.toReal := Set.uIcc_of_le (hlo.trans hhi)
  by_cases hEq : ρ j = (box j).lo.toReal
  · have hupd : updR ρ j ((box j).lo.toReal) = ρ := by rw [← hEq]; exact updR_self
    refine hface ρ ?_
    have hx := boxMem_faceBoxLo (box := box) (j := j) hρ
    rwa [hupd] at hx
  · have hlt : (box j).lo.toReal < ρ j := hlo.lt_of_ne (Ne.symm hEq)
    have hseg : ContinuousOn (fun x => f (updR ρ j x))
        (Set.Icc (box j).lo.toReal (ρ j)) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      refine ((hmaster ρ hρ y hy1 (hy2.trans hhi)).continuousWithinAt).mono ?_
      intro z hz
      rw [hlohi]
      exact ⟨hz.1, hz.2.trans hhi⟩
    have hdiff : ∀ t ∈ Set.Ioo (box j).lo.toReal (ρ j),
        HasDerivAt (fun x => f (updR ρ j x)) (d (updR ρ j t)) t := by
      intro t ht
      have hnh : Set.uIcc (box j).lo.toReal (box j).hi.toReal ∈ nhds t :=
        Filter.mem_of_superset (Ioo_mem_nhds ht.1 (lt_of_lt_of_le ht.2 hhi))
          (fun z hz => Set.mem_uIcc_of_le hz.1.le hz.2.le)
      exact (hmaster ρ hρ t ht.1.le (ht.2.le.trans hhi)).hasDerivAt hnh
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
      (f := fun x => f (updR ρ j x)) (f' := fun x => d (updR ρ j x)) hlt hseg hdiff
    have hcbox : boxMem box (updR ρ j c) :=
      boxMem_updR hρ ⟨hc.1.le, hc.2.le.trans hhi⟩
    have hfacev : 0 < f (updR ρ j ((box j).lo.toReal)) :=
      hface _ (boxMem_faceBoxLo hρ)
    have hkey := congrArg (fun v => (ρ j - (box j).lo.toReal) * v) hslope
    rw [updR_self] at hkey
    have hpos' : 0 < f ρ - f (updR ρ j ((box j).lo.toReal)) := by
      have hs2 := congrArg (fun v => v * (ρ j - (box j).lo.toReal)) hslope
      rw [updR_self, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')] at hs2
      rw [← hs2]
      exact mul_pos (hdpos _ hcbox) (sub_pos.mpr hlt)
    linarith

/-- **facePos 核心引理（hi 面，`∂ⱼf < 0`）**：对称版本——`d` 全盒严格负、
`f` 在 hi 面盒严格正 ⇒ `f` 全盒严格正。
`f(ρ) − f(ρ[j←hi]) = −(hi − ρⱼ)·|d(线段上某点)| > 0`。 -/
theorem facePosHi {n : ℕ} {box : Fin n → DInterval} {j : Fin n}
    {f d : (Fin n → ℝ) → ℝ}
    (hmaster : ∀ ρ : Fin n → ℝ, boxMem box ρ → ∀ x : ℝ, (box j).lo.toReal ≤ x →
      x ≤ (box j).hi.toReal →
      HasDerivWithinAt (fun x' => f (updR ρ j x')) (d (updR ρ j x))
        (Set.uIcc (box j).lo.toReal (box j).hi.toReal) x)
    (hdneg : ∀ ρ : Fin n → ℝ, boxMem box ρ → d ρ < 0)
    (hface : ∀ ρ : Fin n → ℝ, boxMem (faceBoxHi box j) ρ → 0 < f ρ)
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) : 0 < f ρ := by
  have hlo : (box j).lo.toReal ≤ ρ j := (hρ j).1
  have hhi : ρ j ≤ (box j).hi.toReal := (hρ j).2
  have hlohi : Set.uIcc (box j).lo.toReal (box j).hi.toReal
      = Set.Icc (box j).lo.toReal (box j).hi.toReal := Set.uIcc_of_le (hlo.trans hhi)
  by_cases hEq : ρ j = (box j).hi.toReal
  · have hupd : updR ρ j ((box j).hi.toReal) = ρ := by rw [← hEq]; exact updR_self
    refine hface ρ ?_
    have hx := boxMem_faceBoxHi (box := box) (j := j) hρ
    rwa [hupd] at hx
  · have hlt : ρ j < (box j).hi.toReal := hhi.lt_of_ne hEq
    have hseg : ContinuousOn (fun x => f (updR ρ j x))
        (Set.Icc (ρ j) (box j).hi.toReal) := by
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      refine ((hmaster ρ hρ y (hlo.trans hy1) hy2).continuousWithinAt).mono ?_
      intro z hz
      rw [hlohi]
      exact ⟨hlo.trans hz.1, hz.2⟩
    have hdiff : ∀ t ∈ Set.Ioo (ρ j) (box j).hi.toReal,
        HasDerivAt (fun x => f (updR ρ j x)) (d (updR ρ j t)) t := by
      intro t ht
      have hnh : Set.uIcc (box j).lo.toReal (box j).hi.toReal ∈ nhds t :=
        Filter.mem_of_superset (Ioo_mem_nhds (lt_of_le_of_lt hlo ht.1) ht.2)
          (fun z hz => Set.mem_uIcc_of_le hz.1.le hz.2.le)
      refine (hmaster ρ hρ t (hlo.trans ht.1.le) ht.2.le).hasDerivAt hnh
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
      (f := fun x => f (updR ρ j x)) (f' := fun x => d (updR ρ j x)) hlt hseg hdiff
    have hcbox : boxMem box (updR ρ j c) :=
      boxMem_updR hρ ⟨hlo.trans hc.1.le, hc.2.le⟩
    have hfacev : 0 < f (updR ρ j ((box j).hi.toReal)) :=
      hface _ (boxMem_faceBoxHi hρ)
    have hkey := congrArg (fun v => ((box j).hi.toReal - ρ j) * v) hslope
    rw [updR_self] at hkey
    have hneg' : f (updR ρ j ((box j).hi.toReal)) - f ρ < 0 := by
      have hs2 := congrArg (fun v => v * ((box j).hi.toReal - ρ j)) hslope
      rw [updR_self, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')] at hs2
      rw [← hs2]
      exact mul_neg_of_neg_of_pos (hdneg _ hcbox) (sub_pos.mpr hlt)
    linarith

/-! ## mono 折叠检查器（组合 checkPosTMHull × 2 + facePos） -/

/-- **mono 折叠检查器（lo 面）**：导数正性叶（`df = ∂ⱼf`，全盒）+ 面叶
（lo 面盒）——两叶 PASS ⇒ 原全盒叶的结论成立（`checkPosFaceLo_sound`）。 -/
def checkPosFaceLo {n : ℕ} (e df : IExpr n) (box : Fin n → DInterval) (j : Fin n)
    (ps psd : TMParams) : Bool :=
  checkPosTMHull df box psd && checkPosTMHull e (faceBoxLo box j) ps

/-- **mono 折叠检查器（hi 面）**：导数负性叶（`IExpr.neg df`，即 `−∂ⱼf`，
全盒）+ 面叶（hi 面盒）——两叶 PASS ⇒ 原全盒叶的结论成立
（`checkPosFaceHi_sound`）。 -/
def checkPosFaceHi {n : ℕ} (e df : IExpr n) (box : Fin n → DInterval) (j : Fin n)
    (ps psd : TMParams) : Bool :=
  checkPosTMHull (IExpr.neg df) box psd && checkPosTMHull e (faceBoxHi box j) ps

/-- **mono 折叠 soundness（lo 面）**：`checkPosFaceLo` 两叶 PASS + `DerivSafeOn`
⇒ `0 < e.evalReal ρ` 对盒上每点成立——原全盒叶被两叶折叠。 -/
theorem checkPosFaceLo_sound {n : ℕ} {e : IExpr n} {box : Fin n → DInterval}
    {j : Fin n} {ps psd : TMParams} (hD : DerivSafeOn box e)
    (h : checkPosFaceLo e (derivIExpr e j) box j ps psd = true)
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) : 0 < e.evalReal ρ := by
  simp only [checkPosFaceLo, Bool.and_eq_true] at h
  obtain ⟨hd, hf⟩ := h
  refine facePosLo (j := j) (f := e.evalReal) (d := (derivIExpr e j).evalReal) ?_ ?_ ?_ hρ
  · intro ρ' hρ' x hx1 hx2
    exact derivIExpr_hasDerivWithinAt hρ' hD hx1 hx2
  · exact fun ρ' hρ' => checkPosTMHull_sound hd ρ' hρ'
  · exact fun ρ' hρ' => checkPosTMHull_sound hf ρ' hρ'

/-- **mono 折叠 soundness（hi 面）**：`checkPosFaceHi` 两叶 PASS + `DerivSafeOn`
⇒ `0 < e.evalReal ρ` 对盒上每点成立。 -/
theorem checkPosFaceHi_sound {n : ℕ} {e : IExpr n} {box : Fin n → DInterval}
    {j : Fin n} {ps psd : TMParams} (hD : DerivSafeOn box e)
    (h : checkPosFaceHi e (derivIExpr e j) box j ps psd = true)
    {ρ : Fin n → ℝ} (hρ : boxMem box ρ) : 0 < e.evalReal ρ := by
  simp only [checkPosFaceHi, Bool.and_eq_true] at h
  obtain ⟨hd, hf⟩ := h
  refine facePosHi (j := j) (f := e.evalReal) (d := (derivIExpr e j).evalReal) ?_ ?_ ?_ hρ
  · intro ρ' hρ' x hx1 hx2
    exact derivIExpr_hasDerivWithinAt hρ' hD hx1 hx2
  · intro ρ' hρ'
    have hv : 0 < -(derivIExpr e j).evalReal ρ' :=
      checkPosTMHull_sound hd ρ' hρ'
    linarith
  · intro ρ' hρ'
    exact checkPosTMHull_sound hf ρ' hρ'


/-! ## 微型端到端（DerivSafeOn 完全放行 + 两叶折叠 ⇒ 语义结论） -/

/- 迷你案例：`f(x, y) = atan(x)/2 − √y + 3/4`，盒 [1/4, 1/2]²。
`∂_y f = −1/(2√y) < 0` ⇒ hi 面折叠；f 在盒上 ≈ 0.165 > 0（hi 面同样为正）。 -/

/-- 迷你表达式。 -/
def miniE : IExpr 2 :=
  .add (.sub (.div (.trans .arctanK (.var 0) 8 (-24)) (.const ⟨2, 0⟩) 0)
      (.sqrt (.var 1) 0 0))
    (.const ⟨3, -2⟩)

/-- 迷你盒 [1/4, 1/2]². -/
def miniBox : Fin 2 → DInterval := fun _ => ⟨⟨64, -8⟩, ⟨128, -8⟩⟩

theorem miniDSafe_div : ∀ ρ : Fin 2 → ℝ, boxMem miniBox ρ →
    (IExpr.const ⟨2, 0⟩).evalReal ρ ≠ 0 := by
  intro ρ _
  simp only [IExpr.evalReal, Dyadic.toReal_two]
  exact Ne.symm (by norm_num : (0 : ℝ) ≠ 2)

theorem miniDSafe_sqrt : ∀ ρ : Fin 2 → ℝ, boxMem miniBox ρ → 0 < ρ 1 := by
  intro ρ hρ
  have h := (hρ 1).1
  have h1 : (miniBox 1).lo.toReal = 1 / 4 := by
    show Dyadic.toReal ⟨64, -8⟩ = 1 / 4
    rw [Dyadic.toReal_def]; norm_num
  rw [h1] at h
  linarith

/-- `DerivSafeOn miniBox miniE` 完全放行（div 常分母 ≠ 0、sqrt 正底、atan）。 -/
theorem miniDSafe : DerivSafeOn miniBox miniE :=
  .add (.sub (.div (.trans (.var 0) (Or.inr (Or.inr rfl)))
      (.const ⟨2, 0⟩) miniDSafe_div)
      (.sqrt (.var 1) miniDSafe_sqrt))
    (.const ⟨3, -2⟩)

/-- 面叶参数（sqrt 证书：√[1/2,1/2] 的 mantissas，recip 粒度 2⁻⁴⁰）。 -/
def miniP : TMParams :=
  ⟨[⟨22, 22, 22, (-40), (-40)⟩], [⟨(-40), (-40), (-40)⟩], [⟨(-40), (-40)⟩]⟩

/-- 导数叶参数（DExpr 含 2 个 sqrt 出现、3 个 div、1 个 atan）。 -/
def miniDP : TMParams :=
  ⟨[⟨19, 19, 16, (-40), (-40)⟩, ⟨19, 19, 16, (-40), (-40)⟩],
    [⟨(-40), (-40), (-40)⟩, ⟨(-40), (-40), (-40)⟩, ⟨(-40), (-40), (-40)⟩],
    [⟨(-40), (-40)⟩]⟩

theorem miniFaceDebug :
    checkPosTMHull miniE (faceBoxHi miniBox 1) miniP = true := by decide

theorem miniDerDebug :
    checkPosTMHull (IExpr.neg (derivIExpr miniE 1)) miniBox miniDP = true := by decide

/-- 两叶 PASS（内核 `decide`）：−∂_y f 全盒正性叶 + hi 面叶。 -/
theorem miniFolded :
    checkPosFaceHi miniE (derivIExpr miniE 1) miniBox 1 miniP miniDP = true := by
  simp only [checkPosFaceHi, Bool.and_eq_true]
  exact ⟨miniDerDebug, miniFaceDebug⟩

/-- 折叠结论：两叶 ⇒ 语义正性（`checkPosFaceHi_sound`，零附加假设）。 -/
theorem miniSemantic (ρ : Fin 2 → ℝ) (hρ : boxMem miniBox ρ) : 0 < miniE.evalReal ρ :=
  checkPosFaceHi_sound miniDSafe miniFolded hρ

#print axioms derivIExpr_hasDerivWithinAt
#print axioms facePosLo
#print axioms facePosHi
#print axioms checkPosFaceLo_sound
#print axioms checkPosFaceHi_sound
#print axioms miniSemantic
#print axioms miniFolded

/-! ## 549 mono 折叠试点（pipeline/interval/emit_diff.py 生成；勿手改）。
自包含：仅 import Kepler.Interval.CertTM（C549HullSpeed 模式）。 -/

namespace Cases


/-- The case expression（逐字复制 C549Hull200.lean 的 C549Hull200Expr；本模块
未 import 该模块，此副本使 mono 折叠叶自包含）. -/

def C549Hull200Expr : IExpr 6 :=

  (.sub (.div (.const ⟨1893, 0⟩) (.const ⟨1000, 0⟩) (-64)) (.add (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.ite (.sub (.abs (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0)) (.trans .arctanK (.div (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (-64)) 128 (-80)) (.ite (.sub (.const ⟨0, 0⟩) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))))) (.sub (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64)) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.ite (.sub (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (.const ⟨0, 0⟩)) (.sub (.neg (.div (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨2, 0⟩) (-64))) (.trans .arctanK (.div (.sqrt (.mul (.mul (.const ⟨4, 0⟩) (.mul (.var 0) (.var 0))) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3))) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4))) (.add (.sub (.add (.add (.sub (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5))) (.sub (.add (.add (.sub (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) (.mul (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))) (.mul (.var 4) (.var 4)))) (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.mul (.var 5) (.var 5)))) (.mul (.mul (.mul (.var 3) (.var 3)) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5))))) 0 0) (.neg (.add (.sub (.add (.add (.sub (.mul (.neg (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 4) (.var 4)))) (.mul (.mul (.var 2) (.var 2)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 4) (.var 4)) (.mul (.var 5) (.var 5)))) (.mul (.mul (.var 0) (.var 0)) (.add (.add (.sub (.add (.add (.neg (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2))) (.mul (.var 3) (.var 3))) (.mul (.var 4) (.var 4))) (.mul (.var 5) (.var 5)))))) (-64)) 128 (-80))) (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))))))))

/-- Cert leaf 0（C549Hull200Leaf1）原盒（逐字复制）. -/

def C549Hull200Box1 : Fin 6 → DInterval :=

  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- Cert leaf 0（C549Hull200Leaf1）原参数（逐字复制）. -/

def C549Hull200P1 : TMParams :=

  ⟨[⟨395358989154285186146491279829791604279813, 93250317514592560731441416803864450113205, 0, (-80), (-80)⟩, ⟨9433584887784091440199691029173883623587746, 9433584887784091440199691029173883623587746, 1153437688406796784244047395759195612193466511351, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- Cert leaf 1（C549Hull200Leaf2）原盒（逐字复制）. -/

def C549Hull200Box2 : Fin 6 → DInterval :=

  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨10264971839, -32⟩⟩]

/-- Cert leaf 1（C549Hull200Leaf2）原参数（逐字复制）. -/

def C549Hull200P2 : TMParams :=

  ⟨[⟨289041520733171477813463328294600964957009, 83864013946173195322829311178716946880065, 0, (-80), (-80)⟩, ⟨8126601043309505651343423202235804014904036, 8126601043309505651343423202235804014904036, 974408654396794624750013399409580923052534877139, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- Cert leaf 2（C549Hull200Leaf3）原盒（逐字复制）. -/

def C549Hull200Box3 : Fin 6 → DInterval :=

  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- Cert leaf 2（C549Hull200Leaf3）原参数（逐字复制）. -/

def C549Hull200P3 : TMParams :=

  ⟨[⟨79133468699060868699517795110745114431523, 620730890222954844068224175594981235936845, 0, (-80), (-80)⟩, ⟨7774449257851452768261384319321526248999473, 7774449257851452768261384319321526248999473, 946376567874961057295770303363452293165239723071, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- Cert leaf 3（C549Hull200Leaf4）原盒（逐字复制）. -/

def C549Hull200Box4 : Fin 6 → DInterval :=

  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩]

/-- Cert leaf 3（C549Hull200Leaf4）原参数（逐字复制）. -/

def C549Hull200P4 : TMParams :=

  ⟨[⟨143613410864391145235403654100673595582358, 593378197390087079180519242036264773772196, 0, (-80), (-80)⟩, ⟨7351370220495064256849005188828458136496871, 7351370220495064256849005188828458136496871, 892623230564725325414475515951890547403108603981, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- Cert leaf 4（C549Hull200Leaf5）原盒（逐字复制）. -/

def C549Hull200Box5 : Fin 6 → DInterval :=

  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- Cert leaf 4（C549Hull200Leaf5）原参数（逐字复制）. -/

def C549Hull200P5 : TMParams :=

  ⟨[⟨73594910277399764572035906309837960160068, 588780465748788289235320747468063808192649, 0, (-80), (-80)⟩, ⟨7341662303369745612261730277056055516154234, 7341662303369745612261730277056055516154234, 892251717986746021938082957686192543176170215266, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/- 符号微分说明：导数叶语句中的 `derivIExpr C549Hull200Expr 2`
由内核在 `decide` 求值（Python 侧镜像 emit_diff.py.dtext 仅用于 stage-A
证书收割；两侧逐 token 一致性由 emit_diff 侧检保证）。求值路径
7 sqrt / 8 div / 2 trans。 -/

/-- Cert leaf 0（C549Hull200Leaf1）的 hi 面盒（x3 钉 hi）. -/
def C549MonoFaceBox1 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

/-- 面叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoPF1 : TMParams :=
  ⟨[⟨428184687208579713573870543835308898408358, 89812461800728597102744006420731751338467, 0, (-80), (-80)⟩, ⟨9370561146449421665598961222648303480225357, 9370561146449421665598961222648303480225357, 1159189064790736625002452126086208537648746192789, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 导数叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoDP1 : TMParams :=
  ⟨[⟨9433584887784091440199691029173883623587746, 9433584887784091440199691029173883623587746, 1153437688406796784244047395759195612193466511351, (-80), (-80)⟩, ⟨9433584887784091440199691029173883623587746, 9433584887784091440199691029173883623587746, 1153437688406796784244047395759195612193466511351, (-80), (-80)⟩, ⟨9433584887784091440199691029173883623587746, 9433584887784091440199691029173883623587746, 1153437688406796784244047395759195612193466511351, (-80), (-80)⟩, ⟨9433584887784091440199691029173883623587746, 9433584887784091440199691029173883623587746, 1153437688406796784244047395759195612193466511351, (-80), (-80)⟩, ⟨9433584887784091440199691029173883623587746, 9433584887784091440199691029173883623587746, 1153437688406796784244047395759195612193466511351, (-80), (-80)⟩, ⟨9433584887784091440199691029173883623587746, 9433584887784091440199691029173883623587746, 1153437688406796784244047395759195612193466511351, (-80), (-80)⟩, ⟨9433584887784091440199691029173883623587746, 9433584887784091440199691029173883623587746, 1153437688406796784244047395759195612193466511351, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 面叶（原表达式于 lo 面盒）. -/
theorem C549MonoFace1 :
    checkPosTMHull C549Hull200Expr (faceBoxLo C549Hull200Box1 2) C549MonoPF1 = true := by
  decide

/-- 导数定号叶（+∂x3f，全盒；导数由内核 `derivIExpr` 求值）. -/
theorem C549MonoDer1 :
    checkPosTMHull (derivIExpr C549Hull200Expr 2)
      C549Hull200Box1 C549MonoDP1 = true := by
  decide

/-- mono 折叠组合（两叶引用，零重算）. -/
theorem C549MonoFold1 :
    checkPosFaceLo C549Hull200Expr (derivIExpr C549Hull200Expr 2)
      C549Hull200Box1 2 C549MonoPF1 C549MonoDP1 = true := by
  simp only [checkPosFaceLo, Bool.and_eq_true]
  exact ⟨C549MonoDer1, C549MonoFace1⟩


/-- Cert leaf 1（C549Hull200Leaf2）的 hi 面盒（x3 钉 hi）. -/
def C549MonoFaceBox2 : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨4853313045, -31⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨10264971839, -32⟩⟩]

/-- 面叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoPF2 : TMParams :=
  ⟨[⟨161393450650724233678125070152485858453037, 80699757978796034658651398710291782644978, 0, (-80), (-80)⟩, ⟨8057810279590882960903979187491222968747682, 8057810279590882960903979187491222968747682, 981174195118675927664331170285278539552523846309, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 导数叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoDP2 : TMParams :=
  ⟨[⟨8126601043309505651343423202235804014904036, 8126601043309505651343423202235804014904036, 974408654396794624750013399409580923052534877139, (-80), (-80)⟩, ⟨8126601043309505651343423202235804014904036, 8126601043309505651343423202235804014904036, 974408654396794624750013399409580923052534877139, (-80), (-80)⟩, ⟨8126601043309505651343423202235804014904036, 8126601043309505651343423202235804014904036, 974408654396794624750013399409580923052534877139, (-80), (-80)⟩, ⟨8126601043309505651343423202235804014904036, 8126601043309505651343423202235804014904036, 974408654396794624750013399409580923052534877139, (-80), (-80)⟩, ⟨8126601043309505651343423202235804014904036, 8126601043309505651343423202235804014904036, 974408654396794624750013399409580923052534877139, (-80), (-80)⟩, ⟨8126601043309505651343423202235804014904036, 8126601043309505651343423202235804014904036, 974408654396794624750013399409580923052534877139, (-80), (-80)⟩, ⟨8126601043309505651343423202235804014904036, 8126601043309505651343423202235804014904036, 974408654396794624750013399409580923052534877139, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 面叶（原表达式于 lo 面盒）. -/
theorem C549MonoFace2 :
    checkPosTMHull C549Hull200Expr (faceBoxLo C549Hull200Box2 2) C549MonoPF2 = true := by
  decide

/-- 导数定号叶（+∂x3f，全盒；导数由内核 `derivIExpr` 求值）. -/
theorem C549MonoDer2 :
    checkPosTMHull (derivIExpr C549Hull200Expr 2)
      C549Hull200Box2 C549MonoDP2 = true := by
  decide

/-- mono 折叠组合（两叶引用，零重算）. -/
theorem C549MonoFold2 :
    checkPosFaceLo C549Hull200Expr (derivIExpr C549Hull200Expr 2)
      C549Hull200Box2 2 C549MonoPF2 C549MonoDP2 = true := by
  simp only [checkPosFaceLo, Bool.and_eq_true]
  exact ⟨C549MonoDer2, C549MonoFace2⟩


/-- Cert leaf 2（C549Hull200Leaf3）的 hi 面盒（x3 钉 hi）. -/
def C549MonoFaceBox3 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨10264971839, -32⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩]

/-- 面叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoPF3 : TMParams :=
  ⟨[⟨86425851228177199878259328613093057355136, 298639804478670655915199463658699844579659, 0, (-80), (-80)⟩, ⟨7723075524064197923177366921727241375526014, 7723075524064197923177366921727241375526014, 951562766442100365846440664437690622071064305426, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 导数叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoDP3 : TMParams :=
  ⟨[⟨7774449257851452768261384319321526248999473, 7774449257851452768261384319321526248999473, 946376567874961057295770303363452293165239723071, (-80), (-80)⟩, ⟨7774449257851452768261384319321526248999473, 7774449257851452768261384319321526248999473, 946376567874961057295770303363452293165239723071, (-80), (-80)⟩, ⟨7774449257851452768261384319321526248999473, 7774449257851452768261384319321526248999473, 946376567874961057295770303363452293165239723071, (-80), (-80)⟩, ⟨7774449257851452768261384319321526248999473, 7774449257851452768261384319321526248999473, 946376567874961057295770303363452293165239723071, (-80), (-80)⟩, ⟨7774449257851452768261384319321526248999473, 7774449257851452768261384319321526248999473, 946376567874961057295770303363452293165239723071, (-80), (-80)⟩, ⟨7774449257851452768261384319321526248999473, 7774449257851452768261384319321526248999473, 946376567874961057295770303363452293165239723071, (-80), (-80)⟩, ⟨7774449257851452768261384319321526248999473, 7774449257851452768261384319321526248999473, 946376567874961057295770303363452293165239723071, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 面叶（原表达式于 lo 面盒）. -/
theorem C549MonoFace3 :
    checkPosTMHull C549Hull200Expr (faceBoxLo C549Hull200Box3 2) C549MonoPF3 = true := by
  decide

/-- 导数定号叶（+∂x3f，全盒；导数由内核 `derivIExpr` 求值）. -/
theorem C549MonoDer3 :
    checkPosTMHull (derivIExpr C549Hull200Expr 2)
      C549Hull200Box3 C549MonoDP3 = true := by
  decide

/-- mono 折叠组合（两叶引用，零重算）. -/
theorem C549MonoFold3 :
    checkPosFaceLo C549Hull200Expr (derivIExpr C549Hull200Expr 2)
      C549Hull200Box3 2 C549MonoPF3 C549MonoDP3 = true := by
  simp only [checkPosFaceLo, Bool.and_eq_true]
  exact ⟨C549MonoDer3, C549MonoFace3⟩


/-- Cert leaf 3（C549Hull200Leaf4）的 hi 面盒（x3 钉 hi）. -/
def C549MonoFaceBox4 : Fin 6 → DInterval :=
  ![⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨2, 0⟩, ⟨17738214933, -33⟩⟩]

/-- 面叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoPF4 : TMParams :=
  ⟨[⟨159726762143511944357856219310108729085807, 569551043695867069496708643026048185035442, 0, (-80), (-80)⟩, ⟨7303762708254732004572029129747147989401810, 7303762708254732004572029129747147989401810, 897852513575616417565878515326033038334786223897, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 导数叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoDP4 : TMParams :=
  ⟨[⟨7351370220495064256849005188828458136496871, 7351370220495064256849005188828458136496871, 892623230564725325414475515951890547403108603981, (-80), (-80)⟩, ⟨7351370220495064256849005188828458136496871, 7351370220495064256849005188828458136496871, 892623230564725325414475515951890547403108603981, (-80), (-80)⟩, ⟨7351370220495064256849005188828458136496871, 7351370220495064256849005188828458136496871, 892623230564725325414475515951890547403108603981, (-80), (-80)⟩, ⟨7351370220495064256849005188828458136496871, 7351370220495064256849005188828458136496871, 892623230564725325414475515951890547403108603981, (-80), (-80)⟩, ⟨7351370220495064256849005188828458136496871, 7351370220495064256849005188828458136496871, 892623230564725325414475515951890547403108603981, (-80), (-80)⟩, ⟨7351370220495064256849005188828458136496871, 7351370220495064256849005188828458136496871, 892623230564725325414475515951890547403108603981, (-80), (-80)⟩, ⟨7351370220495064256849005188828458136496871, 7351370220495064256849005188828458136496871, 892623230564725325414475515951890547403108603981, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 面叶（原表达式于 lo 面盒）. -/
theorem C549MonoFace4 :
    checkPosTMHull C549Hull200Expr (faceBoxLo C549Hull200Box4 2) C549MonoPF4 = true := by
  decide

/-- 导数定号叶（+∂x3f，全盒；导数由内核 `derivIExpr` 求值）. -/
theorem C549MonoDer4 :
    checkPosTMHull (derivIExpr C549Hull200Expr 2)
      C549Hull200Box4 C549MonoDP4 = true := by
  decide

/-- mono 折叠组合（两叶引用，零重算）. -/
theorem C549MonoFold4 :
    checkPosFaceLo C549Hull200Expr (derivIExpr C549Hull200Expr 2)
      C549Hull200Box4 2 C549MonoPF4 C549MonoDP4 = true := by
  simp only [checkPosFaceLo, Bool.and_eq_true]
  exact ⟨C549MonoDer4, C549MonoFace4⟩


/-- Cert leaf 4（C549Hull200Leaf5）的 hi 面盒（x3 钉 hi）. -/
def C549MonoFaceBox5 : Fin 6 → DInterval :=
  ![⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨10264971839, -32⟩, ⟨10264971839, -32⟩⟩, ⟨⟨10264971839, -32⟩, ⟨21088289427, -33⟩⟩, ⟨⟨4853313045, -31⟩, ⟨19971597929, -33⟩⟩, ⟨⟨18854906431, -33⟩, ⟨4853313045, -31⟩⟩]

/-- 面叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoPF5 : TMParams :=
  ⟨[⟨40462380467009956670147352113147735011115, 565779416547605316502123990747896429257651, 0, (-80), (-80)⟩, ⟨7291664119663343229017658317083247812945569, 7291664119663343229017658317083247812945569, 897322461277949853543379330310330066337569170623, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 导数叶参数（stage-A 收割，verdict PASS）. -/
def C549MonoDP5 : TMParams :=
  ⟨[⟨7341662303369745612261730277056055516154234, 7341662303369745612261730277056055516154234, 892251717986746021938082957686192543176170215266, (-80), (-80)⟩, ⟨7341662303369745612261730277056055516154234, 7341662303369745612261730277056055516154234, 892251717986746021938082957686192543176170215266, (-80), (-80)⟩, ⟨7341662303369745612261730277056055516154234, 7341662303369745612261730277056055516154234, 892251717986746021938082957686192543176170215266, (-80), (-80)⟩, ⟨7341662303369745612261730277056055516154234, 7341662303369745612261730277056055516154234, 892251717986746021938082957686192543176170215266, (-80), (-80)⟩, ⟨7341662303369745612261730277056055516154234, 7341662303369745612261730277056055516154234, 892251717986746021938082957686192543176170215266, (-80), (-80)⟩, ⟨7341662303369745612261730277056055516154234, 7341662303369745612261730277056055516154234, 892251717986746021938082957686192543176170215266, (-80), (-80)⟩, ⟨7341662303369745612261730277056055516154234, 7341662303369745612261730277056055516154234, 892251717986746021938082957686192543176170215266, (-80), (-80)⟩], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], [⟨(-80), (-80)⟩, ⟨(-80), (-80)⟩]⟩

/-- 面叶（原表达式于 lo 面盒）. -/
theorem C549MonoFace5 :
    checkPosTMHull C549Hull200Expr (faceBoxLo C549Hull200Box5 2) C549MonoPF5 = true := by
  decide

/-- 导数定号叶（+∂x3f，全盒；导数由内核 `derivIExpr` 求值）. -/
theorem C549MonoDer5 :
    checkPosTMHull (derivIExpr C549Hull200Expr 2)
      C549Hull200Box5 C549MonoDP5 = true := by
  decide

/-- mono 折叠组合（两叶引用，零重算）. -/
theorem C549MonoFold5 :
    checkPosFaceLo C549Hull200Expr (derivIExpr C549Hull200Expr 2)
      C549Hull200Box5 2 C549MonoPF5 C549MonoDP5 = true := by
  simp only [checkPosFaceLo, Bool.and_eq_true]
  exact ⟨C549MonoDer5, C549MonoFace5⟩



#print axioms C549MonoFace1
#print axioms C549MonoDer1
#print axioms C549MonoFold1
#print axioms C549MonoFold2
#print axioms C549MonoFold3
#print axioms C549MonoFold4
#print axioms C549MonoFold5

end Cases

end Kepler.Interval
