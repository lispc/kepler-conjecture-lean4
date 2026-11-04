/-
  Kepler.T11Glue — lane `terminal11-w1`: 20 "certificate in library, glue
  pending" items of `main_nonlinear_terminal_v11` (route A of
  docs/scouts/terminal11-scout.md §2.1; T0 named statements landed in
  Kepler.Text.LocalAuto1 at a522078c).

  Each `glue_*` theorem closes one T0 named statement
  `Kepler.Text.mainEstimate_*` from its in-library G4 certificate leaf
  (`Kepler.Interval.Cases.C*`, zero-sorry `decide`+kernel shard trees):
  - premise slot: the cert `_pos` theorem applied at x = y² (or y itself for
    the y-space original form 4717061266);
  - one-line substitution: `evalReal` identity pinning the emitted expression
    as the signed prep body (`deltaX` / `deltaX4` / `deltaX1` / `cayleytr`)
    at x (all 20 bodies are pure polynomials — verified term by term);
  - endpoint embedding: the squared y-box lies inside the cert box (dyadic
    outward expansions; `nlinarith`/`linarith` + `norm_num`).

  The 19 prep-form certs are consumed on the squared box, which is exactly
  the prep form the HOL pipeline emitted (`prep-<idv>`); no y2x semantic
  bridge is needed beyond `deltaY = deltaX ∘ sq` / `delta4Y = deltaX4 ∘ sq`
  / `yOfX` (all definitional in Kepler.Text.SphereKit).

  Machine cost of the certificate shards was already paid (oleans in
  .lake/build/lib/lean/Kepler/Interval/Cases/ at the work HEAD).
-/
import Kepler.Interval.Cases.C1117202051
import Kepler.Interval.Cases.C1348932091delta
import Kepler.Interval.Cases.C2073661826
import Kepler.Interval.Cases.C2125338128M
import Kepler.Interval.Cases.C2171548893
import Kepler.Interval.Cases.C2485876245a
import Kepler.Interval.Cases.C2485876245b
import Kepler.Interval.Cases.C3078028960
import Kepler.Interval.Cases.C4559601669
import Kepler.Interval.Cases.C4559601669b
import Kepler.Interval.Cases.C4680581274deltacayleytr0
import Kepler.Interval.Cases.C4680581274deltatopissue
import Kepler.Interval.Cases.C4717061266
import Kepler.Interval.Cases.C5550839403delta
import Kepler.Interval.Cases.C5557288534delta
import Kepler.Interval.Cases.C6184614449
import Kepler.Interval.Cases.C8346775862
import Kepler.Interval.Cases.C8495326405
import Kepler.Interval.Cases.C8631418063
import Kepler.Interval.Cases.C9368433105
import Kepler.Text.LocalAuto1

namespace Terminal11W1

open Kepler.Interval


/-- Cert leaf `C2125338128M`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C2125338128M (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C2125338128MExpr).evalReal ρ
      = Kepler.Text.deltaX (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) := by
  dsimp only [Kepler.Interval.Cases.C2125338128MExpr, IExpr.evalReal, Kepler.Text.deltaX]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C2125338128M : Kepler.Text.mainEstimate_2125338128 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C2125338128MBox ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C2125338128M_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C2125338128M] at hpos
  exact hpos

/-- Cert leaf `C8495326405`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C8495326405 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C8495326405Expr).evalReal ρ
      = -(Kepler.Text.deltaX (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) := by
  dsimp only [Kepler.Interval.Cases.C8495326405Expr, IExpr.evalReal, Kepler.Text.deltaX]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C8495326405 : Kepler.Text.mainEstimate_8495326405 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h0v : (2 : ℝ) * Kepler.Text.h0 = (2.52 : ℝ) := by norm_num [Kepler.Text.h0]
  have h0w : (4 : ℝ) * Kepler.Text.h0 = (5.04 : ℝ) := by norm_num [Kepler.Text.h0]
  simp only [h0v] at h5l h5h
  have hmem : boxMem Kepler.Interval.Cases.C8495326405Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨9728208299, -30⟩, ⟨36, 0⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨6818690079, -30⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨9728208299, -30⟩, ⟨36, 0⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C8495326405_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C8495326405] at hpos
  have hc : (0 : ℝ) < -Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := hpos
  show Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
  linarith

/-- Cert leaf `C2171548893`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C2171548893 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C2171548893Expr).evalReal ρ
      = -(Kepler.Text.deltaX (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) := by
  dsimp only [Kepler.Interval.Cases.C2171548893Expr, IExpr.evalReal, Kepler.Text.deltaX]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C2171548893 : Kepler.Text.mainEstimate_2171548893 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C2171548893Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨9728208299, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨7035371179, -29⟩, ⟨36, 0⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨9728208299, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨7035371179, -29⟩, ⟨36, 0⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C2171548893_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C2171548893] at hpos
  have hc : (0 : ℝ) < -Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := hpos
  show Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
  linarith

/-- Cert leaf `C4680581274deltatopissue`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C4680581274deltatopissue (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C4680581274deltatopissueExpr).evalReal ρ
      = -(Kepler.Text.deltaX (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) := by
  dsimp only [Kepler.Interval.Cases.C4680581274deltatopissueExpr, IExpr.evalReal, Kepler.Text.deltaX]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C4680581274deltatopissue : Kepler.Text.mainEstimate_4680581274_delta_top_issue := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C4680581274deltatopissueBox ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨5381355651, -29⟩, ⟨16, 0⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨9728208299, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨5381355651, -29⟩, ⟨16, 0⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C4680581274deltatopissue_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C4680581274deltatopissue] at hpos
  have hc : (0 : ℝ) < -Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := hpos
  show Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
  linarith

/-- Verbatim copy of goal 1 of `Kepler.Interval.Cases.C4680581274deltacayleytr0Goals`. -/
private def g_cay0_1 : IExpr 6 := (.sub (.const ⟨0, 0⟩) (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.mul (.mul (.mul (.const ⟨2, 0⟩) (.var 3)) (.const ⟨4, 0⟩)) (.const ⟨4, 0⟩)) (.mul (.mul (.mul (.mul (.const ⟨2, 0⟩) (.var 3)) (.var 4)) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.neg (.const ⟨1, 0⟩)) (.mul (.mul (.const ⟨1, 0⟩) (.var 3)) (.var 3))) (.const ⟨0, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 5)) (.var 3)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 5)) (.var 3)) (.var 4))) (.mul (.mul (.const ⟨2, 0⟩) (.var 5)) (.mul (.mul (.const ⟨1, 0⟩) (.var 3)) (.var 3)))) (.mul (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 0)) (.var 3)) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 0)) (.var 3)) (.const ⟨4, 0⟩))) (.mul (.mul (.const ⟨2, 0⟩) (.var 0)) (.mul (.mul (.const ⟨1, 0⟩) (.var 3)) (.var 3)))) (.mul (.mul (.mul (.const ⟨4, 0⟩) (.var 0)) (.var 5)) (.var 3))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 1)) (.const ⟨4, 0⟩)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 1)) (.var 4)) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.mul (.const ⟨4, 0⟩) (.var 1)) (.var 4)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.const ⟨2, 0⟩) (.var 1)) (.var 3)) (.const ⟨0, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 1)) (.var 3)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 1)) (.var 3)) (.var 4))) (.mul (.mul (.mul (.const ⟨2, 0⟩) (.var 1)) (.var 5)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 1)) (.var 5)) (.var 4))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 1)) (.var 5)) (.var 3))) (.mul (.mul (.mul (.mul (.const ⟨2, 0⟩) (.var 1)) (.var 0)) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 1)) (.var 0)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 1)) (.var 0)) (.var 3))) (.mul (.mul (.neg (.const ⟨1, 0⟩)) (.mul (.mul (.const ⟨1, 0⟩) (.var 1)) (.var 1))) (.const ⟨0, 0⟩))) (.mul (.mul (.const ⟨2, 0⟩) (.mul (.mul (.const ⟨1, 0⟩) (.var 1)) (.var 1))) (.const ⟨4, 0⟩))) (.mul (.mul (.const ⟨2, 0⟩) (.mul (.mul (.const ⟨1, 0⟩) (.var 1)) (.var 1))) (.var 4))) (.mul (.mul (.mul (.mul (.const ⟨4, 0⟩) (.var 2)) (.const ⟨4, 0⟩)) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.const ⟨4, 0⟩)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 4)) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.mul (.const ⟨2, 0⟩) (.var 2)) (.var 3)) (.const ⟨0, 0⟩))) (.mul (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 3)) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 3)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 5)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.const ⟨2, 0⟩) (.var 2)) (.var 5)) (.var 4))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 5)) (.var 3))) (.mul (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 0)) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.mul (.const ⟨2, 0⟩) (.var 2)) (.var 0)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 0)) (.var 3))) (.mul (.mul (.mul (.const ⟨2, 0⟩) (.var 2)) (.var 1)) (.const ⟨0, 0⟩))) (.mul (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 1)) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 1)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 1)) (.const ⟨4, 0⟩))) (.mul (.mul (.mul (.neg (.const ⟨2, 0⟩)) (.var 2)) (.var 1)) (.var 4))) (.mul (.mul (.mul (.const ⟨4, 0⟩) (.var 2)) (.var 1)) (.var 3))) (.mul (.mul (.neg (.const ⟨1, 0⟩)) (.mul (.mul (.const ⟨1, 0⟩) (.var 2)) (.var 2))) (.const ⟨0, 0⟩))) (.mul (.mul (.mul (.const ⟨2, 0⟩) (.mul (.mul (.const ⟨1, 0⟩) (.var 2)) (.var 2))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64))) (.div (.const ⟨301, 0⟩) (.const ⟨100, 0⟩) (-64)))) (.mul (.mul (.const ⟨2, 0⟩) (.mul (.mul (.const ⟨1, 0⟩) (.var 2)) (.var 2))) (.const ⟨4, 0⟩))))

/-- Verbatim copy of goal 2 of `Kepler.Interval.Cases.C4680581274deltacayleytr0Goals`. -/
private def g_cay0_2 : IExpr 6 := (.sub (.const ⟨0, 0⟩) (.add (.mul (.const ⟨1, 0⟩) (.const ⟨10, 0⟩)) (.mul (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.var 0) (.var 3)) (.add (.add (.sub (.add (.add (.neg (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.const ⟨4, 0⟩))) (.mul (.mul (.var 1) (.var 4)) (.add (.sub (.add (.add (.sub (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.const ⟨4, 0⟩)))) (.mul (.mul (.var 2) (.const ⟨4, 0⟩)) (.sub (.add (.add (.sub (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.const ⟨4, 0⟩)))) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (.mul (.mul (.var 0) (.var 2)) (.var 4))) (.mul (.mul (.var 0) (.var 1)) (.const ⟨4, 0⟩))) (.mul (.mul (.var 3) (.var 4)) (.const ⟨4, 0⟩))) (.neg (.const ⟨1, 0⟩)))))

/-- Verbatim copy of goal 3 of `Kepler.Interval.Cases.C4680581274deltacayleytr0Goals`. -/
private def g_cay0_3 : IExpr 6 := (.sub (.const ⟨0, 0⟩) (.mul (.add (.sub (.add (.add (.sub (.mul (.neg (.var 1)) (.var 2)) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.const ⟨4, 0⟩))) (.mul (.var 4) (.const ⟨4, 0⟩))) (.mul (.var 0) (.add (.add (.sub (.add (.add (.neg (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.const ⟨4, 0⟩)))) (.neg (.const ⟨1, 0⟩))))

private theorem goals_cay0 : Kepler.Interval.Cases.C4680581274deltacayleytr0Goals = [DisjGoal.pos g_cay0_1, DisjGoal.pos g_cay0_2, DisjGoal.pos g_cay0_3] := rfl

private theorem eval_g_cay0_1v (x1 x2 x3 x4 x5 x7 : ℝ) :
    (g_cay0_1).evalReal ![x1, x2, x3, x4, x5, x7]
      = -Kepler.Text.cayleytr_t11 x3 x2 x1 x7 x4 x5 (4 : ℝ) (4 : ℝ) (9.0601 : ℝ) (0 : ℝ) := by
  dsimp only [g_cay0_1, IExpr.evalReal, Kepler.Text.cayleytr_t11]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val']
  all_goals ring

private theorem eval_g_cay0_2v (x1 x2 x3 x4 x5 x7 : ℝ) :
    (g_cay0_2).evalReal ![x1, x2, x3, x4, x5, x7]
      = Kepler.Text.deltaX x1 x2 x3 x4 x5 (4 : ℝ) - (10 : ℝ) := by
  dsimp only [g_cay0_2, IExpr.evalReal, Kepler.Text.deltaX]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val']
  all_goals ring

private theorem eval_g_cay0_3v (x1 x2 x3 x4 x5 x7 : ℝ) :
    (g_cay0_3).evalReal ![x1, x2, x3, x4, x5, x7]
      = Kepler.Text.deltaX4 x1 x2 x3 x4 x5 (4 : ℝ) := by
  dsimp only [g_cay0_3, IExpr.evalReal, Kepler.Text.deltaX4]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val']
  all_goals ring

theorem glue_C4680581274deltacayleytr0 :
    Kepler.Text.mainEstimate_4680581274_delta_issue_cayleytr0 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h h7l h7h h8l h8h h9l h9h
  have hv635 : (2.0 : ℝ) * (1.26 : ℝ) * (2.0 : ℝ) * (1.26 : ℝ) = (6.3504 : ℝ) := by norm_num
  have hv906 : (3.01 : ℝ) * (3.01 : ℝ) = (9.0601 : ℝ) := by norm_num
  have hv316 : (3.166 : ℝ) * (3.166 : ℝ) = (10.023556 : ℝ) := by norm_num
  simp only [hv635] at h1h h2h h3h h7h
  simp only [hv906] at h4l h9l h9h
  simp only [hv316] at h4h
  have hx5 : x5 = (4 : ℝ) := by linarith
  have hx6 : x6 = (4 : ℝ) := by linarith
  have hx8 : x8 = (4 : ℝ) := by linarith
  have hx9 : x9 = (3.01 : ℝ) * (3.01 : ℝ) := by linarith
  rw [hv906] at hx9
  have hmem : boxMem Kepler.Interval.Cases.C4680581274deltacayleytr0Box ![x1, x2, x3, x4, x5, x7] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem x1
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem x2
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem x3
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h3l, h3h]
    · show (⟨⟨9728208299, -30⟩, ⟨10762711303, -30⟩⟩ : DInterval).mem x4
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem x5
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem x7
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h7l, h7h]
  obtain ⟨g, hg, hge⟩ := Kepler.Interval.Cases.C4680581274deltacayleytr0_pos ![x1, x2, x3, x4, x5, x7] hmem
  rw [goals_cay0] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · simp only [Kepler.Interval.DisjGoal.eval] at hge
    rw [eval_g_cay0_1v] at hge
    refine Or.inl ?_
    show Kepler.Text.cayleytr_t11 x3 x2 x1 x7 x4 x5 x8 x6 x9 (0 : ℝ) < (0 : ℝ)
    rw [hx8, hx6, hx9]
    linarith
  · simp only [Kepler.Interval.DisjGoal.eval] at hge
    rw [eval_g_cay0_2v] at hge
    refine Or.inr (Or.inl ?_)
    show (10 : ℝ) + Kepler.Text.deltaX x1 x2 x3 x4 x5 x6 * (-1 : ℝ) < (0 : ℝ)
    rw [hx6]
    linarith
  · simp only [Kepler.Interval.DisjGoal.eval] at hge
    rw [eval_g_cay0_3v] at hge
    refine Or.inr (Or.inr ?_)
    show Kepler.Text.deltaX4 x1 x2 x3 x4 x5 x6 * (-1 : ℝ) < (0 : ℝ)
    rw [hx6]
    linarith

/-- Cert leaf `C5550839403delta`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C5550839403delta (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C5550839403deltaExpr).evalReal ρ
      = Kepler.Text.deltaX (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) := by
  dsimp only [Kepler.Interval.Cases.C5550839403deltaExpr, IExpr.evalReal, Kepler.Text.deltaX]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C5550839403delta : Kepler.Text.mainEstimate_5550839403_delta := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h0v : (2 : ℝ) * Kepler.Text.h0 = (2.52 : ℝ) := by norm_num [Kepler.Text.h0]
  have h0w : (4 : ℝ) * Kepler.Text.h0 = (5.04 : ℝ) := by norm_num [Kepler.Text.h0]
  simp only [h0v] at h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C5550839403deltaBox ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨9728208299, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨9728208299, -30⟩, ⟨13531831337, -30⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C5550839403delta_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C5550839403delta] at hpos
  exact hpos

/-- Cert leaf `C9368433105`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C9368433105 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C9368433105Expr).evalReal ρ
      = Kepler.Text.deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) := by
  dsimp only [Kepler.Interval.Cases.C9368433105Expr, IExpr.evalReal, Kepler.Text.deltaX4]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C9368433105 : Kepler.Text.mainEstimate_9368433105 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h0v : (2 : ℝ) * Kepler.Text.h0 = (2.52 : ℝ) := by norm_num [Kepler.Text.h0]
  have h0w : (4 : ℝ) * Kepler.Text.h0 = (5.04 : ℝ) := by norm_num [Kepler.Text.h0]
  simp only [h0v] at h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C9368433105Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨9728208299, -30⟩, ⟨13531831337, -30⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨6818690079, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C9368433105_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C9368433105] at hpos
  exact hpos

/-- Cert leaf `C5557288534delta`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C5557288534delta (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C5557288534deltaExpr).evalReal ρ
      = Kepler.Text.deltaX (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) := by
  dsimp only [Kepler.Interval.Cases.C5557288534deltaExpr, IExpr.evalReal, Kepler.Text.deltaX]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C5557288534delta : Kepler.Text.mainEstimate_5557288534_delta := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C5557288534deltaBox ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨9728208299, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨9728208299, -30⟩, ⟨730815529, -26⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C5557288534delta_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C5557288534delta] at hpos
  exact hpos

/-- Cert leaf `C1348932091delta`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C1348932091delta (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C1348932091deltaExpr).evalReal ρ
      = Kepler.Text.deltaX (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) := by
  dsimp only [Kepler.Interval.Cases.C1348932091deltaExpr, IExpr.evalReal, Kepler.Text.deltaX]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C1348932091delta : Kepler.Text.mainEstimate_1348932091_delta := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C1348932091deltaBox ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨6818690079, -30⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨9728208299, -30⟩, ⟨730815529, -26⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C1348932091delta_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C1348932091delta] at hpos
  exact hpos

/-- Cert leaf `C2073661826`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C2073661826 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C2073661826Expr).evalReal ρ
      = -(Kepler.Text.deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) := by
  dsimp only [Kepler.Interval.Cases.C2073661826Expr, IExpr.evalReal, Kepler.Text.deltaX4]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C2073661826 : Kepler.Text.mainEstimate_2073661826 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h0v : (2 : ℝ) * Kepler.Text.h0 = (2.52 : ℝ) := by norm_num [Kepler.Text.h0]
  have h0w : (4 : ℝ) * Kepler.Text.h0 = (5.04 : ℝ) := by norm_num [Kepler.Text.h0]
  simp only [h0w] at h4l h4h
  have hmem : boxMem Kepler.Interval.Cases.C2073661826Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨1691478917, -27⟩, ⟨27274760317, -30⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨6818690079, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C2073661826_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C2073661826] at hpos
  have hc : (0 : ℝ) < -Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := hpos
  show Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
  linarith

/-- Cert leaf `C6184614449`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C6184614449 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C6184614449Expr).evalReal ρ
      = -(Kepler.Text.deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) := by
  dsimp only [Kepler.Interval.Cases.C6184614449Expr, IExpr.evalReal, Kepler.Text.deltaX4]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C6184614449 : Kepler.Text.mainEstimate_6184614449 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h0v : (2 : ℝ) * Kepler.Text.h0 = (2.52 : ℝ) := by norm_num [Kepler.Text.h0]
  have h0w : (4 : ℝ) * Kepler.Text.h0 = (5.04 : ℝ) := by norm_num [Kepler.Text.h0]
  simp only [h0v] at h1l h1h h2l h2h h3l h3h h5l h5h h6l h6h
  simp only [h0w] at h4l h4h
  have hmem : boxMem Kepler.Interval.Cases.C6184614449Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨11693048463, -30⟩, ⟨27274760317, -30⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C6184614449_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C6184614449] at hpos
  have hc : (0 : ℝ) < -Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := hpos
  show Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
  linarith

/-- Cert leaf `C8631418063`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C8631418063 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C8631418063Expr).evalReal ρ
      = Kepler.Text.deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) := by
  dsimp only [Kepler.Interval.Cases.C8631418063Expr, IExpr.evalReal, Kepler.Text.deltaX4]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C8631418063 : Kepler.Text.mainEstimate_8631418063 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h0v : (2 : ℝ) * Kepler.Text.h0 = (2.52 : ℝ) := by norm_num [Kepler.Text.h0]
  have h0w : (4 : ℝ) * Kepler.Text.h0 = (5.04 : ℝ) := by norm_num [Kepler.Text.h0]
  simp only [h0v] at h1l h1h h2l h2h h3l h3h
  have hmem : boxMem Kepler.Interval.Cases.C8631418063Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨9728208299, -30⟩, ⟨16457482529, -30⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C8631418063_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C8631418063] at hpos
  exact hpos

/-- Verbatim copy of goal 1 of `Kepler.Interval.Cases.C8346775862Goals`. -/
private def g_C8346775862_1 : IExpr 6 := (.sub (.const ⟨0, 0⟩) (.add (.mul (.const ⟨1, 0⟩) (.const ⟨200, 0⟩)) (.mul (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.var 0) (.var 3)) (.add (.add (.sub (.add (.add (.neg (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5))) (.mul (.mul (.var 1) (.var 4)) (.add (.sub (.add (.add (.sub (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)))) (.mul (.mul (.var 2) (.var 5)) (.sub (.add (.add (.sub (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)))) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (.mul (.mul (.var 0) (.var 2)) (.var 4))) (.mul (.mul (.var 0) (.var 1)) (.var 5))) (.mul (.mul (.var 3) (.var 4)) (.var 5))) (.neg (.const ⟨1, 0⟩)))))

private def g_C8346775862_2 : IExpr 6 := (.sub (.const ⟨0, 0⟩) (.add (.sub (.add (.add (.sub (.mul (.neg (.var 1)) (.var 2)) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 5))) (.mul (.var 4) (.var 5))) (.mul (.var 0) (.add (.add (.sub (.add (.add (.neg (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)))))

private theorem goals_C8346775862 : Kepler.Interval.Cases.C8346775862Goals = [DisjGoal.pos g_C8346775862_1, DisjGoal.pos g_C8346775862_2] := rfl

private theorem eval_g_C8346775862_1v (y1 y2 y3 y4 y5 y6 : ℝ) :
    (g_C8346775862_1).evalReal ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] = Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) - (200 : ℝ) := by
  dsimp only [g_C8346775862_1, IExpr.evalReal, Kepler.Text.deltaX, Kepler.Text.deltaX4]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val']
  all_goals ring

private theorem eval_g_C8346775862_2v (y1 y2 y3 y4 y5 y6 : ℝ) :
    (g_C8346775862_2).evalReal ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] = -Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
  dsimp only [g_C8346775862_2, IExpr.evalReal, Kepler.Text.deltaX, Kepler.Text.deltaX4]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val']
  all_goals ring

theorem glue_C8346775862 : Kepler.Text.mainEstimate_8346775862 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h0v : (2 : ℝ) * Kepler.Text.h0 = (2.52 : ℝ) := by norm_num [Kepler.Text.h0]
  have h0w : (4 : ℝ) * Kepler.Text.h0 = (5.04 : ℝ) := by norm_num [Kepler.Text.h0]
  simp only [h0v] at h1l h1h h2l h2h h3l h3h
  have hmem : boxMem Kepler.Interval.Cases.C8346775862Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨9728208299, -30⟩, ⟨16457482529, -30⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  obtain ⟨g, hg, hge⟩ := Kepler.Interval.Cases.C8346775862_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [goals_C8346775862] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp only [Kepler.Interval.DisjGoal.eval] at hge
    rw [eval_g_C8346775862_1v] at hge
    refine Or.inl ?_
    show (200 : ℝ) < Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
    linarith
  · simp only [Kepler.Interval.DisjGoal.eval] at hge
    rw [eval_g_C8346775862_2v] at hge
    refine Or.inr ?_
    show Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
    linarith

/-- Verbatim copy of goal 1 of `Kepler.Interval.Cases.C3078028960Goals`. -/
private def g_C3078028960_1 : IExpr 6 := (.sub (.const ⟨0, 0⟩) (.add (.add (.sub (.sub (.add (.mul (.neg (.var 0)) (.var 3)) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 4))) (.mul (.var 1) (.var 5))) (.mul (.var 2) (.var 5))) (.mul (.var 3) (.add (.add (.sub (.add (.add (.neg (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)))))

private def g_C3078028960_2 : IExpr 6 := (.sub (.const ⟨0, 0⟩) (.add (.mul (.const ⟨1, 0⟩) (.const ⟨20, 0⟩)) (.mul (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.var 0) (.var 3)) (.add (.add (.sub (.add (.add (.neg (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5))) (.mul (.mul (.var 1) (.var 4)) (.add (.sub (.add (.add (.sub (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)))) (.mul (.mul (.var 2) (.var 5)) (.sub (.add (.add (.sub (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)))) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (.mul (.mul (.var 0) (.var 2)) (.var 4))) (.mul (.mul (.var 0) (.var 1)) (.var 5))) (.mul (.mul (.var 3) (.var 4)) (.var 5))) (.neg (.const ⟨1, 0⟩)))))

private theorem goals_C3078028960 : Kepler.Interval.Cases.C3078028960Goals = [DisjGoal.pos g_C3078028960_1, DisjGoal.pos g_C3078028960_2] := rfl

private theorem eval_g_C3078028960_1v (y1 y2 y3 y4 y5 y6 : ℝ) :
    (g_C3078028960_1).evalReal ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] = -Kepler.Text.deltaX1_t11 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
  dsimp only [g_C3078028960_1, IExpr.evalReal, Kepler.Text.deltaX1_t11, Kepler.Text.deltaX]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val']
  all_goals ring

private theorem eval_g_C3078028960_2v (y1 y2 y3 y4 y5 y6 : ℝ) :
    (g_C3078028960_2).evalReal ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] = Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) - (20 : ℝ) := by
  dsimp only [g_C3078028960_2, IExpr.evalReal, Kepler.Text.deltaX1_t11, Kepler.Text.deltaX]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val']
  all_goals ring

theorem glue_C3078028960 : Kepler.Text.mainEstimate_3078028960 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C3078028960Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨9728208299, -30⟩, ⟨16457482529, -30⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  obtain ⟨g, hg, hge⟩ := Kepler.Interval.Cases.C3078028960_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [goals_C3078028960] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp only [Kepler.Interval.DisjGoal.eval] at hge
    rw [eval_g_C3078028960_1v] at hge
    refine Or.inl ?_
    show Kepler.Text.deltaX1_t11 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
    linarith
  · simp only [Kepler.Interval.DisjGoal.eval] at hge
    rw [eval_g_C3078028960_2v] at hge
    refine Or.inr ?_
    show (20 : ℝ) < Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
    linarith

/-- Verbatim copy of goal 1 of `Kepler.Interval.Cases.C2485876245bGoals`. -/
private def g_C2485876245b_1 : IExpr 6 := (.sub (.const ⟨0, 0⟩) (.mul (.add (.sub (.add (.add (.sub (.mul (.neg (.var 1)) (.var 2)) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 4))) (.mul (.var 2) (.var 5))) (.mul (.var 4) (.var 5))) (.mul (.var 0) (.add (.add (.sub (.add (.add (.neg (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)))) (.neg (.const ⟨1, 0⟩))))

private def g_C2485876245b_2 : IExpr 6 := (.sub (.const ⟨0, 0⟩) (.sub (.sub (.sub (.sub (.add (.add (.mul (.mul (.var 0) (.var 3)) (.add (.add (.sub (.add (.add (.neg (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5))) (.mul (.mul (.var 1) (.var 4)) (.add (.sub (.add (.add (.sub (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)))) (.mul (.mul (.var 2) (.var 5)) (.sub (.add (.add (.sub (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)) (.var 5)))) (.mul (.mul (.var 1) (.var 2)) (.var 3))) (.mul (.mul (.var 0) (.var 2)) (.var 4))) (.mul (.mul (.var 0) (.var 1)) (.var 5))) (.mul (.mul (.var 3) (.var 4)) (.var 5))))

private theorem goals_C2485876245b : Kepler.Interval.Cases.C2485876245bGoals = [DisjGoal.pos g_C2485876245b_1, DisjGoal.pos g_C2485876245b_2] := rfl

private theorem eval_g_C2485876245b_1v (y1 y2 y3 y4 y5 y6 : ℝ) :
    (g_C2485876245b_1).evalReal ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] = Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
  dsimp only [g_C2485876245b_1, IExpr.evalReal, Kepler.Text.deltaX4, Kepler.Text.deltaX]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val']
  all_goals ring

private theorem eval_g_C2485876245b_2v (y1 y2 y3 y4 y5 y6 : ℝ) :
    (g_C2485876245b_2).evalReal ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] = -Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
  dsimp only [g_C2485876245b_2, IExpr.evalReal, Kepler.Text.deltaX4, Kepler.Text.deltaX]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val']
  all_goals ring

theorem glue_C2485876245b : Kepler.Text.mainEstimate_2485876245b := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C2485876245bBox ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨9728208299, -30⟩, ⟨27274760317, -30⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  obtain ⟨g, hg, hge⟩ := Kepler.Interval.Cases.C2485876245b_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [goals_C2485876245b] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp only [Kepler.Interval.DisjGoal.eval] at hge
    rw [eval_g_C2485876245b_1v] at hge
    refine Or.inl ?_
    exact hge
  · simp only [Kepler.Interval.DisjGoal.eval] at hge
    rw [eval_g_C2485876245b_2v] at hge
    refine Or.inr ?_
    show Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
    linarith

/-- Cert leaf `C2485876245a`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C2485876245a (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C2485876245aExpr).evalReal ρ
      = Kepler.Text.deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) := by
  dsimp only [Kepler.Interval.Cases.C2485876245aExpr, IExpr.evalReal, Kepler.Text.deltaX4]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C2485876245a : Kepler.Text.mainEstimate_2485876245a := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C2485876245aBox ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨9, 0⟩, ⟨27274760317, -30⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C2485876245a_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C2485876245a] at hpos
  exact hpos

/-- Cert leaf `C4559601669b`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C4559601669b (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C4559601669bExpr).evalReal ρ
      = -(Kepler.Text.deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) := by
  dsimp only [Kepler.Interval.Cases.C4559601669bExpr, IExpr.evalReal, Kepler.Text.deltaX4]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C4559601669b : Kepler.Text.mainEstimate_4559601669b := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C4559601669bBox ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨9728208299, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C4559601669b_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C4559601669b] at hpos
  have hc : (0 : ℝ) < -Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := hpos
  show Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
  linarith

/-- Cert leaf `C4559601669`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C4559601669 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C4559601669Expr).evalReal ρ
      = -(Kepler.Text.deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) := by
  dsimp only [Kepler.Interval.Cases.C4559601669Expr, IExpr.evalReal, Kepler.Text.deltaX4]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C4559601669 : Kepler.Text.mainEstimate_4559601669 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C4559601669Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨9728208299, -30⟩, ⟨16457482529, -30⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C4559601669_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C4559601669] at hpos
  have hc : (0 : ℝ) < -Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := hpos
  show Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
  linarith

/-- Cert leaf `C1117202051`: prep form; `evalReal` is the (signed) body at x. -/
private theorem eval_C1117202051 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C1117202051Expr).evalReal ρ
      = -(Kepler.Text.deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) := by
  dsimp only [Kepler.Interval.Cases.C1117202051Expr, IExpr.evalReal, Kepler.Text.deltaX4]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C1117202051 : Kepler.Text.mainEstimate_1117202051 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C1117202051Box ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1l, h1h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2l, h2h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3l, h3h]
    · show (⟨⟨9728208299, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4l, h4h]
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5l, h5h]
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C1117202051_pos ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] hmem
  rw [eval_C1117202051] at hpos
  have hc : (0 : ℝ) < -Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := hpos
  show Kepler.Text.deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) < (0 : ℝ)
  linarith

private theorem eval_C4717061266 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C4717061266Expr).evalReal ρ
      = Kepler.Text.deltaY (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) := by
  dsimp only [Kepler.Interval.Cases.C4717061266Expr, IExpr.evalReal, Kepler.Text.deltaY, Kepler.Text.deltaX]
  simp only [Dyadic.toReal_int]
  ring

theorem glue_C4717061266 : Kepler.Text.mainEstimate_4717061266 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h0v : (2 : ℝ) * Kepler.Text.h0 = (2.52 : ℝ) := by norm_num [Kepler.Text.h0]
  simp only [h0v] at h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem : boxMem Kepler.Interval.Cases.C4717061266Box ![y1, y2, y3, y4, y5, y6] := by
    intro i
    fin_cases i
    · show (⟨⟨2, 0⟩, ⟨2705829397, -30⟩⟩ : DInterval).mem y1
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h1l, h1h]
    · show (⟨⟨2, 0⟩, ⟨2705829397, -30⟩⟩ : DInterval).mem y2
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h2l, h2h]
    · show (⟨⟨2, 0⟩, ⟨2705829397, -30⟩⟩ : DInterval).mem y3
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h3l, h3h]
    · show (⟨⟨2, 0⟩, ⟨2705829397, -30⟩⟩ : DInterval).mem y4
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h4l, h4h]
    · show (⟨⟨2, 0⟩, ⟨2705829397, -30⟩⟩ : DInterval).mem y5
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h5l, h5h]
    · show (⟨⟨2, 0⟩, ⟨2705829397, -30⟩⟩ : DInterval).mem y6
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> linarith [h6l, h6h]
  have hpos := Kepler.Interval.Cases.C4717061266_pos ![y1, y2, y3, y4, y5, y6] hmem
  rw [eval_C4717061266] at hpos
  exact hpos


-- Per-item axiom probes (expected: exactly [propext, Classical.choice, Quot.sound]).
#print axioms glue_C2125338128M
#print axioms glue_C8495326405
#print axioms glue_C2171548893
#print axioms glue_C4680581274deltatopissue
#print axioms glue_C4680581274deltacayleytr0
#print axioms glue_C5550839403delta
#print axioms glue_C9368433105
#print axioms glue_C5557288534delta
#print axioms glue_C1348932091delta
#print axioms glue_C2073661826
#print axioms glue_C6184614449
#print axioms glue_C8631418063
#print axioms glue_C8346775862
#print axioms glue_C3078028960
#print axioms glue_C2485876245b
#print axioms glue_C2485876245a
#print axioms glue_C4559601669b
#print axioms glue_C4559601669
#print axioms glue_C1117202051
#print axioms glue_C4717061266
end Terminal11W1
