/-
LocalAuto7W12N: W12(b2b-ii-b3c 前) — `FF'rev` 侧轨道闭合（`p12j_face_rev` 的四个件）。

* `p12n_R_iter_mem`（私）：`r^[n] w ∈ V'`（迭代保 `V'`）；
* `p12n_pre_iter_mem`（私）：`pre^[n] w ∈ V'`；
* `p12m_pre_rho_iter`：`pre^[n] (r^[n] w) = w`（`pre` 迭代是 `r` 迭代在 `V'` 上的左逆）；
* `p12n_pre_orbit_any`：任意基点 `z ∈ V'` 的 `pre`-轨道覆盖 `V'`（`∃ n, pre^[n] z = w`）；
* `p12m_pre_orbit`：`∃ n, pre^[n] w0 = w`（`p12n_pre_orbit_any` 取 `z := w0` 的特例）；
* `p12m_ff_rev_iter`：`ff^[n] (r w, w) = (r (pre^[n] w), pre^[n] w)`；
* `p12j_face_rev`：`x ∈ FF'rev ⇒ orbitF ff x = FF'rev`（双向）。

口径：`p12m_pre_orbit`、`p12j_face_rev` 带 `hcard3 : 3 ≤ V'.ncard`（经 `p12m_r_iter_mod`）。
W12E–M、LA7 零改动。
-/
import Kepler.Text.LocalAuto7W12M

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- `r^[n] w ∈ V'`（W12G 私件的本地副本）。 -/
private theorem p12n_R_iter_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v) :
    ∀ n : ℕ, (p12b_R FF v)^[n] w0 ∈ p12b_V V v := by
  intro n
  induction n with
  | zero => simpa using hw0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact p12b_R_mem hcl hedge hv ih

/-- `pre^[n] w ∈ V'`（`pre` 保 `V'` 的迭代形式）。 -/
private theorem p12n_pre_iter_mem {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    ∀ (n : ℕ) {w : V3}, w ∈ p12b_V V v → (p12e_pre hcl hedge hv)^[n] w ∈ p12b_V V v := by
  intro n
  induction n with
  | zero => intro w hw; simpa using hw
  | succ k ih =>
    intro w hw
    rw [Function.iterate_succ_apply']
    exact (p12e_pre_spec hcl hedge hv (ih hw)).1

/-- `pre^[n] (r^[n] w) = w`：`pre` 迭代是 `r` 迭代在 `V'` 上的左逆。 -/
theorem p12m_pre_rho_iter {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    ∀ (n : ℕ) {w : V3}, w ∈ p12b_V V v →
      (p12e_pre hcl hedge hv)^[n] ((p12b_R FF v)^[n] w) = w := by
  intro n
  induction n with
  | zero => intro w hw; rfl
  | succ k ih =>
    intro w hw
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [p12m_pre_rho hcl hedge hv
      (p12n_R_iter_mem hcl hedge hv hw k)]
    exact ih hw

/-- 任意基点 `z ∈ V'`：`pre`-轨道覆盖 `V'`（`∃ n, pre^[n] z = w`）。 -/
theorem p12n_pre_orbit_any {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    ∀ z ∈ p12b_V V v, ∀ w ∈ p12b_V V v,
      ∃ n : ℕ, (p12e_pre hcl hedge hv)^[n] z = w := by
  intro z hz w hw
  have hV' : orbitF_p2 (p12b_R FF v) z = p12b_V V v :=
    p12d_orbit_splice_V hcl hedge hv hz
  have hworb : w ∈ orbitF_p2 (p12b_R FF v) z := by rw [hV']; exact hw
  obtain ⟨j, hj⟩ := hworb
  obtain ⟨hper, -⟩ := p12g_period hcl hedge hv hz
  have hk_pos : 0 < (p12b_V V v).ncard := by omega
  have hjle : j % (p12b_V V v).ncard ≤ (p12b_V V v).ncard :=
    le_of_lt (Nat.mod_lt j hk_pos)
  set n : ℕ := (p12b_V V v).ncard - j % (p12b_V V v).ncard with hn
  have hnj : n + j % (p12b_V V v).ncard = (p12b_V V v).ncard :=
    Nat.sub_add_cancel hjle
  have hjmod : (p12b_R FF v)^[j % (p12b_V V v).ncard] z = w := by
    rw [← p12m_r_iter_mod hcl hedge hv hz hcard3 j]
    exact hj
  have hrz : (p12b_R FF v)^[n] w = z := by
    rw [← hjmod]
    calc (p12b_R FF v)^[n] ((p12b_R FF v)^[j % (p12b_V V v).ncard] z)
        = (p12b_R FF v)^[n + j % (p12b_V V v).ncard] z :=
          (Function.iterate_add_apply _ _ _ _).symm
      _ = (p12b_R FF v)^[(p12b_V V v).ncard] z := by rw [hnj]
      _ = z := hper
  exact ⟨n, by rw [← hrz]; exact p12m_pre_rho_iter hcl hedge hv n hw⟩

/-- `pre`-轨道从 `w0` 出发覆盖 `V'`：`∀ w ∈ V', ∃ n, pre^[n] w0 = w`。 -/
theorem p12m_pre_orbit {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v w0 : V3} (hv : v ∈ V) (hw0 : w0 ∈ p12b_V V v)
    (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    ∀ w ∈ p12b_V V v, ∃ n : ℕ, (p12e_pre hcl hedge hv)^[n] w0 = w :=
  fun w hw => p12n_pre_orbit_any hcl hedge hv hcard3 w0 hw0 w hw

/-- `ff^[n] (r w, w) = (r (pre^[n] w), pre^[n] w)`（反向 dart 的迭代公式）。 -/
theorem p12m_ff_rev_iter {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) :
    ∀ (n : ℕ) {w : V3}, w ∈ p12b_V V v →
      (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v))^[n]
          (p12b_R FF v w, w)
        = (p12b_R FF v ((p12e_pre hcl hedge hv)^[n] w),
            (p12e_pre hcl hedge hv)^[n] w) := by
  intro n
  induction n with
  | zero => intro w hw; rfl
  | succ k ih =>
    intro w hw
    rw [Function.iterate_succ_apply', ih hw]
    have hpk : (p12e_pre hcl hedge hv)^[k] w ∈ p12b_V V v :=
      p12n_pre_iter_mem hcl hedge hv k hw
    rw [p12i_ff_step_rev hcl hedge hv hpk]
    rw [Function.iterate_succ_apply']
    exact Prod.ext (p12e_pre_spec hcl hedge hv hpk).2.symm rfl

/-- **`p12j_face_rev`（FF'rev 侧）**：`x ∈ FF'rev ⇒ orbitF ff x = FF'rev`。 -/
theorem p12j_face_rev {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (hcl : ConvexLocalFan V E FF) (hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E)
    {v : V3} (hv : v ∈ V) (hcard3 : 3 ≤ (p12b_V V v).ncard) :
    ∀ x ∈ p12f_FFrev V FF v,
      orbitF_p3 (ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v)) x
        = p12f_FFrev V FF v := by
  intro x hx
  set ff := ffOfHyp_p3 (0:V3) (p12b_V V v) (p12b_E V FF v) with hff
  obtain ⟨w, hw, rfl⟩ := hx
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    rw [p12m_ff_rev_iter hcl hedge hv n hw]
    exact ⟨(p12e_pre hcl hedge hv)^[n] w, p12n_pre_iter_mem hcl hedge hv n hw, rfl⟩
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨n, hn⟩ := p12n_pre_orbit_any hcl hedge hv hcard3 w hw w' hw'
    refine ⟨n, ?_⟩
    rw [p12m_ff_rev_iter hcl hedge hv n hw, hn]

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p12m_pre_rho_iter
#print axioms Kepler.Text.p12n_pre_orbit_any
#print axioms Kepler.Text.p12m_pre_orbit
#print axioms Kepler.Text.p12m_ff_rev_iter
#print axioms Kepler.Text.p12j_face_rev

end Kepler.Text
