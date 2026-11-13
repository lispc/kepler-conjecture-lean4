/-
YebwjngKit — VASYYAU wave 0 (lane vasw0-w1): two small proved links.

HOL sources:
  * `scripts/local/VASYYAU.hl:292-381` `YEBWJNG` — with `a p (p+1) = &2` and
    both `p`, `p + 1` non-straight, the endpoint distance is `&2`.  The fan
    assembly mirrors `VasTuaKit.TUAPYYU1_vaskit`; the engine is
    `CUXVZOZ_p21` at `k = 4`, `p1 := p`.
  * `trig2.hl:1050-1090` `ARCV_INEQUALTY` (= `KEITDWB`) — the angle
    triangle inequality `arcV p u v ≤ arcV p u x + arcV p x v`
    (Cauchy–Schwarz core), consumed by ASSWPOW / VASYYAU 2b-i.

The LA25 `YEBWJNG_p25` re-export cannot be discharged in place: the kit
imports LA21/26/28/33/34, all of which sit downstream of LocalAuto25 in
the import DAG (cycle via LocalAuto27).  The real proof is therefore
consumed through the LocalConcl `YEBWJNG_discharged` wiring.
-/
import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto9
import Kepler.Text.LocalAuto14
import Kepler.Text.LocalAuto21
import Kepler.Text.LocalAuto26
import Kepler.Text.LocalAuto28
import Kepler.Text.LocalAuto33
import Kepler.Text.LocalAuto34
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-- HOL `YEBWJNG` (VASYYAU.hl:292-381): with `s.a p (p + 1) = 2` and both
`p`, `p + 1` non-straight, the endpoint distance equals `2`. -/
theorem YEBWJNG_kit (h : main_nonlinear_terminal_v11) (s : ScsV39)
    (v : ℕ → V3) (p : ℕ) (his : isScsV39 s)
    (hbasic : scsBasicV39 s) (hk : s.k = 4) (hv : v ∈ MMsV39 s)
    (hdiag : ∀ i j, scsDiag 4 i j → s.a i j ≤ cstab ∧ cstab < dist (v i) (v j) ∧
      4 * h0 < s.b i j)
    (hval : ∀ i, (s.a i (i + 1) = 2 ∧ s.b i (i + 1) = 2 * h0) ∨
      (s.a i (i + 1) = 2 * h0 ∧ s.b i (i + 1) = cstab))
    (h1 : ¬scsIsStr s v p) (h2 : ¬scsIsStr s v (p + 1)) (ha : s.a p (p + 1) = 2) :
    dist (v p) (v (p + 1)) = 2 := by
  let FF : Set (V3 × V3) := Set.range fun i => (v i, v (i + 1))
  have hFF : Set.range (fun i => (v i, v (i + 1))) = FF := rfl
  have hgen : scsGeneric v := GSXRFWM_p33 s v his hk hv
  have hBB : BBsV39 s v := MMS_IMP_BBS_p28 s v hv
  have hper : Periodic v 4 := by
    have h := hBB.2.1
    rw [hk] at h
    exact h
  have hcl : ConvexLocalFan (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF :=
    BBS_IMP_CONVEX_LOCAL_FAN_p34 s 4 v (by omega) hk hBB
  have hcl2 : convexLocalFan_p2 (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF := w15_clf2 hcl
  -- the rho/ivs values on the successor-dart fan
  have hbij : ∀ j, rhoNode1 FF (v j) = v (j + 1) ∧ ivsRhoNode1 FF (v j) = v (j + 3) := by
    intro j
    obtain ⟨h1, h2⟩ := BB_RHO_NODE_IVS_p26 s 4 v (v j) (Set.range v)
      (Set.range fun i => ({v i, v (i + 1)} : Set V3)) FF j hk rfl rfl rfl hFF his
      (by omega) hBB
    exact ⟨h1, by rw [h2, show j + 4 - 1 = j + 3 by omega]⟩
  -- the azim bound (convex local fan)
  have hle : ∀ j, azim 0 (v j) (v (j + 1)) (v (j + 3)) ≤ Real.pi := by
    intro j
    have h0 := IN_V_IMP_AZIM_LESS_PI (V := Set.range v)
      (E := Set.range fun i => ({v i, v (i + 1)} : Set V3)) (FF := FF)
      hcl2 (v j) ⟨j, rfl⟩ (v (j + 3)) ⟨j + 3, rfl⟩
    rw [show rhoNode1_p2 FF (v j) = v (j + 1) by
      rw [show rhoNode1_p2 FF (v j) = rhoNode1 FF (v j) from rfl, (hbij j).1]] at h0
    exact h0
  -- `¬scsIsStr` gives the strict inequality at the same index
  have hstr_ne : ∀ j, ¬scsIsStr s v j →
      azim 0 (v j) (v (j + 1)) (v (j + 3)) ≠ Real.pi := by
    intro j hj he
    apply hj
    unfold scsIsStr
    rw [hk]
    simpa [show j + (4 - 1) = j + 3 by omega] using he
  have hang : ∀ j, ¬scsIsStr s v j → interiorAngle1 0 FF (v j) < Real.pi := by
    intro j hj
    have h1 := hle j
    have h2 := hstr_ne j hj
    rw [interiorAngle1, (hbij j).1, (hbij j).2]
    exact lt_of_le_of_ne h1 h2
  -- the `a`/`b` value table at the closing edge `(p + 3, p + 4 ≡ p)`
  have hh0 : h0 = 1.26 := rfl
  have hp4 : v (p + 4) = v p := by
    rw [← periodic_mod_eq_p23 hper (p + 4), ← periodic_mod_eq_p23 hper p]
    congr 1
    omega
  have hedge := hBB.2.2.1 (p + 3) (p + 4)
  rw [hp4] at hedge
  have hbnd_a : (2 : ℝ) ≤ s.a (p + 3) (p + 4) := by
    rcases hval (p + 3) with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [ha']
    · rw [ha', hh0]; norm_num
  have hbnd_b : s.b (p + 3) (p + 4) ≤ cstab := by
    rcases hval (p + 3) with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [hb', hh0]; unfold cstab; norm_num
    · rw [hb']
  have h2e : 2 ≤ dist (v (p + 3)) (v p) := hbnd_a.trans hedge.1
  have hdc : dist (v (p + 3)) (v p) ≤ cstab := hedge.2.trans hbnd_b
  -- the diagonal across the quad
  have hd1 : scsDiag 4 (p + 1) (p + 3) := SCS_DIAG_4_ADD2_p33 p
  have hbd := (hdiag _ _ hd1).2.1
  have hc3 : (3 : ℝ) < cstab := by unfold cstab; norm_num
  have hd : 3 ≤ dist (v (p + (4 - 1))) (v (p + 1)) := by
    rw [show p + (4 - 1) = p + 3 by omega, dist_comm]
    exact le_trans hc3.le hbd.le
  have ha' : ∀ i j, scsDiag 4 i j → psort 4 (i, j) ≠ psort 4 (p + 3, p + 1) →
      s.a i j < dist (v i) (v j) := fun i j hd _ =>
    lt_of_le_of_lt (hdiag _ _ hd).1 (hdiag _ _ hd).2.1
  have hb' : ∀ i j, scsDiag 4 i j → 4 * h0 < s.b i j := fun i j hd =>
    (hdiag _ _ hd).2.2
  have hcase : Real.pi / 2 < interiorAngle1 0 FF (v p) ∨
      interiorAngle1 0 FF (v (p + 1)) < Real.pi := Or.inr (hang (p + 1) h2)
  have hb12 : s.b p (p + 1) ≤ 2 * h0 := by
    rcases hval p with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
    · rw [hb2]
    · rw [ha2] at ha
      norm_num [hh0] at ha
  exact CUXVZOZ_p21 h s FF 4 p v rfl his hk.symm (by omega) hv hbasic hgen
    hd ha' hb' (hang p h1) hcase ha hb12 h2e hdc

/-- HOL `KEITDWB` = `ARCV_INEQUALTY` (trig2.hl:1050-1090): the angle
triangle inequality, `arcV p u v ≤ arcV p u x + arcV p x v`.  The
Cauchy–Schwarz core of the HOL proof is `InnerProductGeometry
.angle_le_angle_add_angle` in Mathlib; this is the bridge through
`arcV p a b = angle (a - p) (b - p)`. -/
theorem KEITDWB_kit (p u v x : V3) (hxp : x ≠ p) (hup : u ≠ p) (hvp : v ≠ p) :
    arcV p u v ≤ arcV p u x + arcV p x v := by
  have hdot : ∀ a b : V3, a ⬝ᵥ b = inner ℝ a b := by
    intro a b
    rw [PiLp.inner_apply, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by
      simp [RCLike.inner_apply, mul_comm]
  have e : ∀ a b : V3, arcV p a b = InnerProductGeometry.angle (a - p) (b - p) := by
    intro a b
    have hnum : (a - p) ⬝ᵥ (b - p) = inner ℝ (a - p) (b - p) := hdot _ _
    have hd1 : dist a p = ‖a - p‖ := dist_eq_norm a p
    have hd2 : dist b p = ‖b - p‖ := dist_eq_norm b p
    show Real.arccos (((a - p) ⬝ᵥ (b - p)) / (dist a p * dist b p)) =
      Real.arccos (inner ℝ (a - p) (b - p) / (‖a - p‖ * ‖b - p‖))
    rw [hnum, hd1, hd2]
  rw [e u v, e u x, e x v]
  exact InnerProductGeometry.angle_le_angle_add_angle (u - p) (x - p) (v - p)

end Kepler.Text
