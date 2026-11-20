/-
Kepler.Text.ZTGJoint0000CornersHM — lane `ztg-joint6-build-w1`, W1
increment 2: the **hminus class** of the `0_0_0_0` corner library.

The 31 corners `(2*hminus, y2…y6)` with at least one further hminus slot
(increment 1 closed the k=0 corner).  Generator-emitted
(`probe/w1b_gen.py`): every numeric claim is exact-rational-verified
before emission; the composition envelopes are ground-truth-checked at
the envelope endpoints and midpoint; all 31 corner side conditions are
verified exactly (`a5 + b5·D < G`).

Structure:
* 17 shared factor lemmas `ztgcHM_f*` — the distinct irreducible
  polynomial factors (in `hminus`) of the 57 tuples' `Δ`/`Δ4`/`A²`;
* 57 `_delta` envelopes (sign-aware interval composition over the
  factor envelopes) and 57 `dihY` two-sided lemmas via the W0
  branch-faithful reduction + the in-tree Taylor brackets (the four
  arctan endpoints use the direct route when `|arg| ≤ 0.7` and the
  π/4 shift (`ztg_atan_shift_add`) otherwise);
* 31 per-corner certificates `ztgcHM_c*` closing
  `0 < ztgMain 0 0 0 0 (2*hminus) y2…y6` through the V5 kit
  (`g4v_corner_value_bounds`) and the W0 pointwise assembly
  (`ztg_main_pos_of_gD`), consuming the increment-1 envelopes
  (`ztgc0000_hm_*`, `ztg_lmfun_hminus_bounds`).

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited.
-/
import Kepler.Text.ZTGJoint0000Corners

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

/-! ## 1. The shared factor envelopes -/

theorem ztgcHM_f0 : ((-708354684284159/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ∧ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ≤ ((-8443717014567343/3051757812500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp3.1, hp4.1, hp2.2, hp3.2, hp4.2]

theorem ztgcHM_f1 : ((4927/4000 : ℝ)) ≤ hminus ∧ hminus ≤ ((15397/12500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  constructor <;> linarith [hh.1, hh.2]

theorem ztgcHM_f2 : ((-7724671/16000000 : ℝ)) ≤ hminus ^ 2 + ((-2/1 : ℝ)) ∧ hminus ^ 2 + ((-2/1 : ℝ)) ≤ ((-75432391/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f3 : ((8825987/16000000 : ℝ)) ≤ ((3/1 : ℝ)) * hminus ^ 2 + ((-4/1 : ℝ)) ∧ ((3/1 : ℝ)) * hminus ^ 2 + ((-4/1 : ℝ)) ≤ ((86202827/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f4 : ((-452354684284159/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ∧ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ≤ ((-5391959202067343/3051757812500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp3.1, hp4.1, hp2.2, hp3.2, hp4.2]

theorem ztgcHM_f5 : ((16275329/8000000 : ℝ)) ≤ ((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ∧ ((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ≤ ((158942609/78125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f6 : ((56825987/16000000 : ℝ)) ≤ ((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ∧ ((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ≤ ((554952827/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f7 : ((-11432831/16000000 : ℝ)) ≤ hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ)) ∧ hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ)) ≤ ((-223286657/312500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f8 : ((40275329/16000000 : ℝ)) ≤ hminus ^ 2 + ((1/1 : ℝ)) ∧ hminus ^ 2 + ((1/1 : ℝ)) ≤ ((393317609/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f9 : ((27983329/16000000 : ℝ)) ≤ hminus ^ 2 + hminus + ((-1/1 : ℝ)) ∧ hminus ^ 2 + hminus + ((-1/1 : ℝ)) ≤ ((273280109/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f10 : ((275329/8000000 : ℝ)) ≤ ((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ)) ∧ ((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ)) ≤ ((2692609/78125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f11 : ((328880027472641/128000000000000 : ℝ)) ≤ ((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ∧ ((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ≤ ((125467480094391899/48828125000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp3.1, hp4.1, hp2.2, hp3.2, hp4.2]

theorem ztgcHM_f12 : ((-23724671/16000000 : ℝ)) ≤ hminus ^ 2 + ((-3/1 : ℝ)) ∧ hminus ^ 2 + ((-3/1 : ℝ)) ≤ ((-231682391/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f13 : ((40825987/16000000 : ℝ)) ≤ ((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ)) ∧ ((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ)) ≤ ((398702827/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcHM_f14 : ((324468456887041/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ∧ hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ≤ ((61893502620438137/48828125000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp3.1, hp4.1, hp2.2, hp3.2, hp4.2]

theorem ztgcHM_f15 : ((-59531543112959/128000000000000 : ℝ)) ≤ ((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ∧ ((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ≤ ((-11348684879561863/24414062500000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp3.1, hp4.1, hp2.2, hp3.2, hp4.2]

theorem ztgcHM_f16 : ((12275329/4000000 : ℝ)) ≤ ((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ)) ∧ ((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ)) ≤ ((119880109/39062500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

/-! ## 2. The 57 tuple reductions and envelopes -/

theorem ztgcHM_t0_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) 2 2 2 2 ∧ deltaY (2 * hminus) (2 * hminus) 2 2 2 2 ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) 2 2 2 2 = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t0 : ((121618696107134461923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 2 2 2 ∧ dihY (2 * hminus) (2 * hminus) 2 2 2 2 ≤ ((243241018979273723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t0_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 2) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((131127670769861329099011/2000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 2) (dlo := ((131127670769861329099011/2000000000000000000000 : ℝ))) (dhi := ((655664209986645209330981/10000000000000000000000 : ℝ)))
    (ulo := (-((48551446323200000000000/131127670769861329099011 : ℝ)))) (uhi := (-((18673330000000000000000/50435708460511169948537 : ℝ))))
    (lo := ((-11081542647611/31250000000000 : ℝ))) (hi := ((-11080976028079/31250000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((131127670769861329099011/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((48551446323200000000000/131127670769861329099011 : ℝ))) * ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((655664209986645209330981/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/50435708460511169948537 : ℝ))) * ((655664209986645209330981/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((48551446323200000000000/131127670769861329099011 : ℝ))) (lo := ((11081542522611/31250000000000 : ℝ))) (hi := ((11081542647611/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-11081542647611/31250000000000 : ℝ)) ≤ Real.arctan (-((48551446323200000000000/131127670769861329099011 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/50435708460511169948537 : ℝ))) (lo := ((11080976028079/31250000000000 : ℝ))) (hi := ((11080976153079/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/50435708460511169948537 : ℝ))) ≤ ((-11080976028079/31250000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t1_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY (2 * hminus) 2 (2 * hminus) 2 2 2 ∧ deltaY (2 * hminus) 2 (2 * hminus) 2 2 2 ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 (2 * hminus) 2 2 2 = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t1 : ((121618696107134461923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 2 2 ∧ dihY (2 * hminus) 2 (2 * hminus) 2 2 2 ≤ ((243241018979273723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t1_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 2) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((131127670769861329099011/2000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 2) (dlo := ((131127670769861329099011/2000000000000000000000 : ℝ))) (dhi := ((655664209986645209330981/10000000000000000000000 : ℝ)))
    (ulo := (-((48551446323200000000000/131127670769861329099011 : ℝ)))) (uhi := (-((18673330000000000000000/50435708460511169948537 : ℝ))))
    (lo := ((-11081542647611/31250000000000 : ℝ))) (hi := ((-11080976028079/31250000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((131127670769861329099011/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((48551446323200000000000/131127670769861329099011 : ℝ))) * ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((655664209986645209330981/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/50435708460511169948537 : ℝ))) * ((655664209986645209330981/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((48551446323200000000000/131127670769861329099011 : ℝ))) (lo := ((11081542522611/31250000000000 : ℝ))) (hi := ((11081542647611/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-11081542647611/31250000000000 : ℝ)) ≤ Real.arctan (-((48551446323200000000000/131127670769861329099011 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/50435708460511169948537 : ℝ))) (lo := ((11080976028079/31250000000000 : ℝ))) (hi := ((11080976153079/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/50435708460511169948537 : ℝ))) ≤ ((-11080976028079/31250000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t2_delta : ((44451674237744075884231/312500000000000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 2 (2 * hminus) 2 2 ∧ deltaY (2 * hminus) 2 2 (2 * hminus) 2 2 ≤ ((434134630659789440331151/3051757812500000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 2 (2 * hminus) 2 2 = ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) ∧ ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) := by
    norm_num
  have hp1 : ((-492704/3125 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) ≤ ((-19708/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-1896540872/9765625 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/125000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((-7300259951546/30517578125 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/500000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  have hp4 : ((-56201051236976881/190734863281250 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/2000000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
  have hp5 : ((44451674237744075884231/312500000000000000000 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((434134630659789440331151/3051757812500000000000 : ℝ)) := by
    have hf := ztgcHM_f2
    constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
  exact hp5

theorem ztgcHM_t2 : ((179483979196087561923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 (2 * hminus) 2 2 ∧ dihY (2 * hminus) 2 2 (2 * hminus) 2 2 ≤ ((358976628550370923847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t2_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-4/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((-20435898085930643/1525878906250000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-4/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-4/1 : ℝ))) ≤ ((-214253738174723/16000000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-20435898085930643/1525878906250000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-4/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-4/1 : ℝ))) ≤ ((-214253738174723/16000000000000 : ℝ)) := by
      have hf := ztgcHM_f3
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 2 = ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((1079079016722061659890673436999/312500000000000000000000000 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((102919258874614375062754135787959/29802322387695312500000000000 : ℝ)) := by
    have hp0 : ((-2048/1 : ℝ)) ≤ ((-2048/1 : ℝ)) ∧ ((-2048/1 : ℝ)) ≤ ((-2048/1 : ℝ)) := by
      norm_num
    have hp1 : ((-7883264/3125 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) ≤ ((-315328/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-30344653952/9765625 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) ≤ ((-48550658/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-116804159224736/30517578125 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/31250000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-449608409895815048/95367431640625 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/125000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((-1730655171791466073514/298023223876953125 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-2903439703632953407/500000000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    have hp6 : ((-13323448840036601566947529/1862645149230957031250 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-14305247419799561436289/2000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp5.1, hp5.2, hf.1, hf.2]
    have hp7 : ((1079079016722061659890673436999/312500000000000000000000000 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((102919258874614375062754135787959/29802322387695312500000000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp6.1, hp6.2, hf.1, hf.2]
    exact hp7
  have hsA : ((293813412160017587546169/5000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 2) ≤ ((587656130769129130181473/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((293813412160017587546169/5000000000000000000000 : ℝ)) ^ 2 ≤ ((1079079016722061659890673436999/312500000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((102919258874614375062754135787959/29802322387695312500000000000 : ℝ)) ≤ ((587656130769129130181473/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| ≤ ((20435898085930643/1525878906250000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_pos_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 2) (dlo := ((293813412160017587546169/5000000000000000000000 : ℝ))) (dhi := ((587656130769129130181473/10000000000000000000000 : ℝ)))
    (ulo := ((10300660489169375000000/45204317751471471552421 : ℝ))) (uhi := ((66964350847977530982400/293813412160017587546169 : ℝ)))
    (lo := ((224043466165979/1000000000000000 : ℝ))) (hi := ((112043407478479/500000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((587656130769129130181473/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((10300660489169375000000/45204317751471471552421 : ℝ)) * ((587656130769129130181473/10000000000000000000000 : ℝ)) ≤ ((214253738174723/16000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((293813412160017587546169/5000000000000000000000 : ℝ))), hE4]
    have hnum : ((20435898085930643/1525878906250000 : ℝ)) ≤ ((66964350847977530982400/293813412160017587546169 : ℝ)) * ((293813412160017587546169/5000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((10300660489169375000000/45204317751471471552421 : ℝ))) (lo := ((224043466165979/1000000000000000 : ℝ))) (hi := ((224043470165979/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : ((224043466165979/1000000000000000 : ℝ)) ≤ Real.arctan ((10300660489169375000000/45204317751471471552421 : ℝ)) := htp.1
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((66964350847977530982400/293813412160017587546169 : ℝ))) (lo := ((112043405478479/500000000000000 : ℝ))) (hi := ((112043407478479/500000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : Real.arctan ((66964350847977530982400/293813412160017587546169 : ℝ)) ≤ ((112043407478479/500000000000000 : ℝ)) := htp.2
    exact hfin

theorem ztgcHM_t3_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY (2 * hminus) 2 2 2 (2 * hminus) 2 ∧ deltaY (2 * hminus) 2 2 2 (2 * hminus) 2 ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 2 2 (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t3 : ((121618696107134461923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 2 (2 * hminus) 2 ∧ dihY (2 * hminus) 2 2 2 (2 * hminus) 2 ≤ ((243241018979273723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t3_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) 2) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((131127670769861329099011/2000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) 2) (dlo := ((131127670769861329099011/2000000000000000000000 : ℝ))) (dhi := ((655664209986645209330981/10000000000000000000000 : ℝ)))
    (ulo := (-((48551446323200000000000/131127670769861329099011 : ℝ)))) (uhi := (-((18673330000000000000000/50435708460511169948537 : ℝ))))
    (lo := ((-11081542647611/31250000000000 : ℝ))) (hi := ((-11080976028079/31250000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((131127670769861329099011/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((48551446323200000000000/131127670769861329099011 : ℝ))) * ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((655664209986645209330981/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/50435708460511169948537 : ℝ))) * ((655664209986645209330981/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((48551446323200000000000/131127670769861329099011 : ℝ))) (lo := ((11081542522611/31250000000000 : ℝ))) (hi := ((11081542647611/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-11081542647611/31250000000000 : ℝ)) ≤ Real.arctan (-((48551446323200000000000/131127670769861329099011 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/50435708460511169948537 : ℝ))) (lo := ((11080976028079/31250000000000 : ℝ))) (hi := ((11080976153079/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/50435708460511169948537 : ℝ))) ≤ ((-11080976028079/31250000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t4_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY (2 * hminus) 2 2 2 2 (2 * hminus) ∧ deltaY (2 * hminus) 2 2 2 2 (2 * hminus) ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 2 2 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t4 : ((121618696107134461923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 2 2 (2 * hminus) ∧ dihY (2 * hminus) 2 2 2 2 (2 * hminus) ≤ ((243241018979273723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t4_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((131127670769861329099011/2000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus)) (dlo := ((131127670769861329099011/2000000000000000000000 : ℝ))) (dhi := ((655664209986645209330981/10000000000000000000000 : ℝ)))
    (ulo := (-((48551446323200000000000/131127670769861329099011 : ℝ)))) (uhi := (-((18673330000000000000000/50435708460511169948537 : ℝ))))
    (lo := ((-11081542647611/31250000000000 : ℝ))) (hi := ((-11080976028079/31250000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((131127670769861329099011/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((48551446323200000000000/131127670769861329099011 : ℝ))) * ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((655664209986645209330981/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/50435708460511169948537 : ℝ))) * ((655664209986645209330981/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((48551446323200000000000/131127670769861329099011 : ℝ))) (lo := ((11081542522611/31250000000000 : ℝ))) (hi := ((11081542647611/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-11081542647611/31250000000000 : ℝ)) ≤ Real.arctan (-((48551446323200000000000/131127670769861329099011 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/50435708460511169948537 : ℝ))) (lo := ((11080976028079/31250000000000 : ℝ))) (hi := ((11080976153079/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/50435708460511169948537 : ℝ))) ≤ ((-11080976028079/31250000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t5_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY 2 (2 * hminus) (2 * hminus) 2 2 2 ∧ deltaY 2 (2 * hminus) (2 * hminus) 2 2 2 ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) (2 * hminus) 2 2 2 = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t5 : ((108254022870072161923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) (2 * hminus) 2 2 2 ∧ dihY 2 (2 * hminus) (2 * hminus) 2 2 2 ≤ ((216518767490720123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t5_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((5391959202067343/190734863281250 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((452354684284159/16000000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((5391959202067343/190734863281250 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((452354684284159/16000000000000 : ℝ)) := by
      have hf := ztgcHM_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 2 = ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 2) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((532282000283584999184133/10000000000000000000000 : ℝ)) ^ 2 ≤ ((270198944466154976/95367431640625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((708354684284159/250000000000 : ℝ)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2))| ≤ ((452354684284159/16000000000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 2) (dlo := ((532282000283584999184133/10000000000000000000000 : ℝ))) (dhi := ((4158583360817583356659/78125000000000000000 : ℝ)))
    (ulo := (-((282721677677599375000000/532282000283584999184133 : ℝ)))) (uhi := (-((116239288903514931200/218872808464083334561 : ℝ))))
    (lo := ((-19530243883767/40000000000000 : ℝ))) (hi := ((-30512655646331/62500000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((532282000283584999184133/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((282721677677599375000000/532282000283584999184133 : ℝ))) * ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ ((-452354684284159/16000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((4158583360817583356659/78125000000000000000 : ℝ))), hE4]
    have hnum : ((-5391959202067343/190734863281250 : ℝ)) ≤ (-((116239288903514931200/218872808464083334561 : ℝ))) * ((4158583360817583356659/78125000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((282721677677599375000000/532282000283584999184133 : ℝ))) (lo := ((19530243723767/40000000000000 : ℝ))) (hi := ((19530243883767/40000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-19530243883767/40000000000000 : ℝ)) ≤ Real.arctan (-((282721677677599375000000/532282000283584999184133 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((116239288903514931200/218872808464083334561 : ℝ))) (lo := ((30512655646331/62500000000000 : ℝ))) (hi := ((30512655896331/62500000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((116239288903514931200/218872808464083334561 : ℝ))) ≤ ((-30512655646331/62500000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t6_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY 2 (2 * hminus) 2 (2 * hminus) 2 2 ∧ deltaY 2 (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) 2 (2 * hminus) 2 2 = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t6 : ((142667879436778461923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 ∧ dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((285338100722834723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t6_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((75432391/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((7724671/1000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((75432391/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((7724671/1000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 2 = ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 2) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((532282000283584999184133/10000000000000000000000 : ℝ)) ^ 2 ≤ ((270198944466154976/95367431640625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((708354684284159/250000000000 : ℝ)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| ≤ ((7724671/1000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 2) (dlo := ((532282000283584999184133/10000000000000000000000 : ℝ))) (dhi := ((4158583360817583356659/78125000000000000000 : ℝ)))
    (ulo := (-((77246710000000000000000/532282000283584999184133 : ℝ)))) (uhi := (-((603459128000000000000/4158583360817583356659 : ℝ))))
    (lo := ((-18014691428389/125000000000000 : ℝ))) (hi := ((-144105824180723/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((532282000283584999184133/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((77246710000000000000000/532282000283584999184133 : ℝ))) * ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ ((-7724671/1000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((4158583360817583356659/78125000000000000000 : ℝ))), hE4]
    have hnum : ((-75432391/9765625 : ℝ)) ≤ (-((603459128000000000000/4158583360817583356659 : ℝ))) * ((4158583360817583356659/78125000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((77246710000000000000000/532282000283584999184133 : ℝ))) (lo := ((18014690928389/125000000000000 : ℝ))) (hi := ((18014691428389/125000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-18014691428389/125000000000000 : ℝ)) ≤ Real.arctan (-((77246710000000000000000/532282000283584999184133 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((603459128000000000000/4158583360817583356659 : ℝ))) (lo := ((144105824180723/1000000000000000 : ℝ))) (hi := ((144105828180723/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((603459128000000000000/4158583360817583356659 : ℝ))) ≤ ((-144105824180723/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t7_delta : ((44451674237744075884231/312500000000000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) 2 2 (2 * hminus) 2 ∧ deltaY 2 (2 * hminus) 2 2 (2 * hminus) 2 ≤ ((434134630659789440331151/3051757812500000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) 2 2 (2 * hminus) 2 = ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) ∧ ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) := by
    norm_num
  have hp1 : ((-492704/3125 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) ≤ ((-19708/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-1896540872/9765625 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/125000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((-7300259951546/30517578125 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/500000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  have hp4 : ((-56201051236976881/190734863281250 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/2000000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
  have hp5 : ((44451674237744075884231/312500000000000000000 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((434134630659789440331151/3051757812500000000000 : ℝ)) := by
    have hf := ztgcHM_f2
    constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
  exact hp5

theorem ztgcHM_t7 : ((73066562407935624769/80000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) 2 2 (2 * hminus) 2 ∧ dihY 2 (2 * hminus) 2 2 (2 * hminus) 2 ≤ ((45668397045010415481/50000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t7_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/4000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((3650129975773/122070312500 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    exact hp4
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) 2 = ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((44451674237744075884231/19531250000000000000 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((434134630659789440331151/190734863281250000000 : ℝ)) := by
    have hp0 : ((-2048/1 : ℝ)) ≤ ((-2048/1 : ℝ)) ∧ ((-2048/1 : ℝ)) ≤ ((-2048/1 : ℝ)) := by
      norm_num
    have hp1 : ((-7883264/3125 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) ≤ ((-315328/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-30344653952/9765625 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) ≤ ((-48550658/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-116804159224736/30517578125 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/31250000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-449608409895815048/95367431640625 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/125000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((44451674237744075884231/19531250000000000000 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((434134630659789440331151/190734863281250000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((477066632287424367235509/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) 2) ≤ ((119271637893974637774703/2500000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((477066632287424367235509/10000000000000000000000 : ℝ)) ^ 2 ≤ ((44451674237744075884231/19531250000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((434134630659789440331151/190734863281250000000 : ℝ)) ≤ ((119271637893974637774703/2500000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) 2) (dlo := ((477066632287424367235509/10000000000000000000000 : ℝ))) (dhi := ((119271637893974637774703/2500000000000000000000 : ℝ)))
    (ulo := (-((368319209386651687321600/477066632287424367235509 : ℝ)))) (uhi := (-((7082831707430781250000/9174741376459587521131 : ℝ))))
    (lo := ((-262985718278280523847/400000000000000000000 : ℝ))) (hi := ((-131485677378937661923/200000000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((477066632287424367235509/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((368319209386651687321600/477066632287424367235509 : ℝ))) * ((477066632287424367235509/10000000000000000000000 : ℝ)) ≤ ((-56201051236976881/1525878906250000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((119271637893974637774703/2500000000000000000000 : ℝ))), hE4]
    have hnum : ((-589291598058241/16000000000000 : ℝ)) ≤ (-((7082831707430781250000/9174741376459587521131 : ℝ))) * ((119271637893974637774703/2500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have hshift : Real.arctan (-((368319209386651687321600/477066632287424367235509 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((108747422900772679913909/845385841674076054557109 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((368319209386651687321600/477066632287424367235509 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((108747422900772679913909/845385841674076054557109 : ℝ))) (lo := ((127933867701747/1000000000000000 : ℝ))) (hi := ((127933871701747/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : ((-262985718278280523847/400000000000000000000 : ℝ)) ≤ Real.arctan (-((368319209386651687321600/477066632287424367235509 : ℝ))) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin
  · have hshift : Real.arctan (-((7082831707430781250000/9174741376459587521131 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((2091909669028806271131/16257573083890368771131 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((7082831707430781250000/9174741376459587521131 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((2091909669028806271131/16257573083890368771131 : ℝ))) (lo := ((3199244312569/25000000000000 : ℝ))) (hi := ((3199244412569/25000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : Real.arctan (-((7082831707430781250000/9174741376459587521131 : ℝ))) ≤ ((-131485677378937661923/200000000000000000000 : ℝ)) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin

theorem ztgcHM_t8_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY 2 (2 * hminus) 2 2 2 (2 * hminus) ∧ deltaY 2 (2 * hminus) 2 2 2 (2 * hminus) ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) 2 2 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t8 : ((102193098010361261923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) 2 2 2 (2 * hminus) ∧ dihY 2 (2 * hminus) 2 2 2 (2 * hminus) ≤ ((204391140781516323847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t8_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 2 (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 2 (2 * hminus)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((532282000283584999184133/10000000000000000000000 : ℝ)) ^ 2 ≤ ((270198944466154976/95367431640625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((708354684284159/250000000000 : ℝ)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((317885218/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 2 (2 * hminus)) (dlo := ((532282000283584999184133/10000000000000000000000 : ℝ))) (dhi := ((4158583360817583356659/78125000000000000000 : ℝ)))
    (ulo := (-((325514463232000000000000/532282000283584999184133 : ℝ)))) (uhi := (-((363288593750000000000/594083337259654765237 : ℝ))))
    (lo := ((-137216336422821/250000000000000 : ℝ))) (hi := ((-109768124777463/200000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((532282000283584999184133/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((325514463232000000000000/532282000283584999184133 : ℝ))) * ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ ((-317885218/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((4158583360817583356659/78125000000000000000 : ℝ))), hE4]
    have hnum : ((-16275329/500000 : ℝ)) ≤ (-((363288593750000000000/594083337259654765237 : ℝ))) * ((4158583360817583356659/78125000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((325514463232000000000000/532282000283584999184133 : ℝ))) (lo := ((137216335422821/250000000000000 : ℝ))) (hi := ((137216336422821/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-137216336422821/250000000000000 : ℝ)) ≤ Real.arctan (-((325514463232000000000000/532282000283584999184133 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((363288593750000000000/594083337259654765237 : ℝ))) (lo := ((109768124777463/200000000000000 : ℝ))) (hi := ((109768125577463/200000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((363288593750000000000/594083337259654765237 : ℝ))) ≤ ((-109768124777463/200000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t9_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY 2 2 (2 * hminus) (2 * hminus) 2 2 ∧ deltaY 2 2 (2 * hminus) (2 * hminus) 2 2 ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY 2 2 (2 * hminus) (2 * hminus) 2 2 = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t9 : ((142667879436778461923/100000000000000000000 : ℝ)) ≤ dihY 2 2 (2 * hminus) (2 * hminus) 2 2 ∧ dihY 2 2 (2 * hminus) (2 * hminus) 2 2 ≤ ((285338100722834723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t9_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((75432391/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((7724671/1000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((75432391/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((7724671/1000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 2 = ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 2) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((532282000283584999184133/10000000000000000000000 : ℝ)) ^ 2 ≤ ((270198944466154976/95367431640625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((708354684284159/250000000000 : ℝ)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| ≤ ((7724671/1000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 2) (dlo := ((532282000283584999184133/10000000000000000000000 : ℝ))) (dhi := ((4158583360817583356659/78125000000000000000 : ℝ)))
    (ulo := (-((77246710000000000000000/532282000283584999184133 : ℝ)))) (uhi := (-((603459128000000000000/4158583360817583356659 : ℝ))))
    (lo := ((-18014691428389/125000000000000 : ℝ))) (hi := ((-144105824180723/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((532282000283584999184133/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((77246710000000000000000/532282000283584999184133 : ℝ))) * ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ ((-7724671/1000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((4158583360817583356659/78125000000000000000 : ℝ))), hE4]
    have hnum : ((-75432391/9765625 : ℝ)) ≤ (-((603459128000000000000/4158583360817583356659 : ℝ))) * ((4158583360817583356659/78125000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((77246710000000000000000/532282000283584999184133 : ℝ))) (lo := ((18014690928389/125000000000000 : ℝ))) (hi := ((18014691428389/125000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-18014691428389/125000000000000 : ℝ)) ≤ Real.arctan (-((77246710000000000000000/532282000283584999184133 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((603459128000000000000/4158583360817583356659 : ℝ))) (lo := ((144105824180723/1000000000000000 : ℝ))) (hi := ((144105828180723/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((603459128000000000000/4158583360817583356659 : ℝ))) ≤ ((-144105824180723/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t10_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY 2 2 (2 * hminus) 2 (2 * hminus) 2 ∧ deltaY 2 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY 2 2 (2 * hminus) 2 (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t10 : ((102193098010361261923/100000000000000000000 : ℝ)) ≤ dihY 2 2 (2 * hminus) 2 (2 * hminus) 2 ∧ dihY 2 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((204391140781516323847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t10_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) 2) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((532282000283584999184133/10000000000000000000000 : ℝ)) ^ 2 ≤ ((270198944466154976/95367431640625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((708354684284159/250000000000 : ℝ)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((317885218/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) 2) (dlo := ((532282000283584999184133/10000000000000000000000 : ℝ))) (dhi := ((4158583360817583356659/78125000000000000000 : ℝ)))
    (ulo := (-((325514463232000000000000/532282000283584999184133 : ℝ)))) (uhi := (-((363288593750000000000/594083337259654765237 : ℝ))))
    (lo := ((-137216336422821/250000000000000 : ℝ))) (hi := ((-109768124777463/200000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((532282000283584999184133/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((325514463232000000000000/532282000283584999184133 : ℝ))) * ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ ((-317885218/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((4158583360817583356659/78125000000000000000 : ℝ))), hE4]
    have hnum : ((-16275329/500000 : ℝ)) ≤ (-((363288593750000000000/594083337259654765237 : ℝ))) * ((4158583360817583356659/78125000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((325514463232000000000000/532282000283584999184133 : ℝ))) (lo := ((137216335422821/250000000000000 : ℝ))) (hi := ((137216336422821/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-137216336422821/250000000000000 : ℝ)) ≤ Real.arctan (-((325514463232000000000000/532282000283584999184133 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((363288593750000000000/594083337259654765237 : ℝ))) (lo := ((109768124777463/200000000000000 : ℝ))) (hi := ((109768125577463/200000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((363288593750000000000/594083337259654765237 : ℝ))) ≤ ((-109768124777463/200000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t11_delta : ((44451674237744075884231/312500000000000000000 : ℝ)) ≤ deltaY 2 2 (2 * hminus) 2 2 (2 * hminus) ∧ deltaY 2 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((434134630659789440331151/3051757812500000000000 : ℝ)) := by
  have hE : deltaY 2 2 (2 * hminus) 2 2 (2 * hminus) = ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) ∧ ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) := by
    norm_num
  have hp1 : ((-492704/3125 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) ≤ ((-19708/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-1896540872/9765625 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/125000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((-7300259951546/30517578125 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/500000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  have hp4 : ((-56201051236976881/190734863281250 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/2000000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
  have hp5 : ((44451674237744075884231/312500000000000000000 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((434134630659789440331151/3051757812500000000000 : ℝ)) := by
    have hf := ztgcHM_f2
    constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
  exact hp5

theorem ztgcHM_t11 : ((73066562407935624769/80000000000000000000 : ℝ)) ≤ dihY 2 2 (2 * hminus) 2 2 (2 * hminus) ∧ dihY 2 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((45668397045010415481/50000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t11_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/4000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((3650129975773/122070312500 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    exact hp4
  have hE2 : 4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 2 (2 * hminus) = ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((44451674237744075884231/19531250000000000000 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((434134630659789440331151/190734863281250000000 : ℝ)) := by
    have hp0 : ((-2048/1 : ℝ)) ≤ ((-2048/1 : ℝ)) ∧ ((-2048/1 : ℝ)) ≤ ((-2048/1 : ℝ)) := by
      norm_num
    have hp1 : ((-7883264/3125 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) ≤ ((-315328/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-30344653952/9765625 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) ≤ ((-48550658/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-116804159224736/30517578125 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/31250000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-449608409895815048/95367431640625 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/125000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((44451674237744075884231/19531250000000000000 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((434134630659789440331151/190734863281250000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((477066632287424367235509/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 2 (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 2 (2 * hminus)) ≤ ((119271637893974637774703/2500000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((477066632287424367235509/10000000000000000000000 : ℝ)) ^ 2 ≤ ((44451674237744075884231/19531250000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((434134630659789440331151/190734863281250000000 : ℝ)) ≤ ((119271637893974637774703/2500000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 2 (2 * hminus)) (dlo := ((477066632287424367235509/10000000000000000000000 : ℝ))) (dhi := ((119271637893974637774703/2500000000000000000000 : ℝ)))
    (ulo := (-((368319209386651687321600/477066632287424367235509 : ℝ)))) (uhi := (-((7082831707430781250000/9174741376459587521131 : ℝ))))
    (lo := ((-262985718278280523847/400000000000000000000 : ℝ))) (hi := ((-131485677378937661923/200000000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((477066632287424367235509/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((368319209386651687321600/477066632287424367235509 : ℝ))) * ((477066632287424367235509/10000000000000000000000 : ℝ)) ≤ ((-56201051236976881/1525878906250000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((119271637893974637774703/2500000000000000000000 : ℝ))), hE4]
    have hnum : ((-589291598058241/16000000000000 : ℝ)) ≤ (-((7082831707430781250000/9174741376459587521131 : ℝ))) * ((119271637893974637774703/2500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have hshift : Real.arctan (-((368319209386651687321600/477066632287424367235509 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((108747422900772679913909/845385841674076054557109 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((368319209386651687321600/477066632287424367235509 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((108747422900772679913909/845385841674076054557109 : ℝ))) (lo := ((127933867701747/1000000000000000 : ℝ))) (hi := ((127933871701747/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : ((-262985718278280523847/400000000000000000000 : ℝ)) ≤ Real.arctan (-((368319209386651687321600/477066632287424367235509 : ℝ))) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin
  · have hshift : Real.arctan (-((7082831707430781250000/9174741376459587521131 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((2091909669028806271131/16257573083890368771131 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((7082831707430781250000/9174741376459587521131 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((2091909669028806271131/16257573083890368771131 : ℝ))) (lo := ((3199244312569/25000000000000 : ℝ))) (hi := ((3199244412569/25000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : Real.arctan (-((7082831707430781250000/9174741376459587521131 : ℝ))) ≤ ((-131485677378937661923/200000000000000000000 : ℝ)) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin

theorem ztgcHM_t12_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY 2 2 2 (2 * hminus) (2 * hminus) 2 ∧ deltaY 2 2 2 (2 * hminus) (2 * hminus) 2 ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY 2 2 2 (2 * hminus) (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t12 : ((142667879436778461923/100000000000000000000 : ℝ)) ≤ dihY 2 2 2 (2 * hminus) (2 * hminus) 2 ∧ dihY 2 2 2 (2 * hminus) (2 * hminus) 2 ≤ ((285338100722834723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t12_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((75432391/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((7724671/1000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((75432391/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((7724671/1000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) 2) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((532282000283584999184133/10000000000000000000000 : ℝ)) ^ 2 ≤ ((270198944466154976/95367431640625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((708354684284159/250000000000 : ℝ)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((7724671/1000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) 2) (dlo := ((532282000283584999184133/10000000000000000000000 : ℝ))) (dhi := ((4158583360817583356659/78125000000000000000 : ℝ)))
    (ulo := (-((77246710000000000000000/532282000283584999184133 : ℝ)))) (uhi := (-((603459128000000000000/4158583360817583356659 : ℝ))))
    (lo := ((-18014691428389/125000000000000 : ℝ))) (hi := ((-144105824180723/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((532282000283584999184133/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((77246710000000000000000/532282000283584999184133 : ℝ))) * ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ ((-7724671/1000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((4158583360817583356659/78125000000000000000 : ℝ))), hE4]
    have hnum : ((-75432391/9765625 : ℝ)) ≤ (-((603459128000000000000/4158583360817583356659 : ℝ))) * ((4158583360817583356659/78125000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((77246710000000000000000/532282000283584999184133 : ℝ))) (lo := ((18014690928389/125000000000000 : ℝ))) (hi := ((18014691428389/125000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-18014691428389/125000000000000 : ℝ)) ≤ Real.arctan (-((77246710000000000000000/532282000283584999184133 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((603459128000000000000/4158583360817583356659 : ℝ))) (lo := ((144105824180723/1000000000000000 : ℝ))) (hi := ((144105828180723/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((603459128000000000000/4158583360817583356659 : ℝ))) ≤ ((-144105824180723/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t13_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY 2 2 2 (2 * hminus) 2 (2 * hminus) ∧ deltaY 2 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY 2 2 2 (2 * hminus) 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t13 : ((142667879436778461923/100000000000000000000 : ℝ)) ≤ dihY 2 2 2 (2 * hminus) 2 (2 * hminus) ∧ dihY 2 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((285338100722834723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t13_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((75432391/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((7724671/1000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((75432391/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((7724671/1000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) 2 (2 * hminus)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((532282000283584999184133/10000000000000000000000 : ℝ)) ^ 2 ≤ ((270198944466154976/95367431640625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((708354684284159/250000000000 : ℝ)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((7724671/1000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) 2 (2 * hminus)) (dlo := ((532282000283584999184133/10000000000000000000000 : ℝ))) (dhi := ((4158583360817583356659/78125000000000000000 : ℝ)))
    (ulo := (-((77246710000000000000000/532282000283584999184133 : ℝ)))) (uhi := (-((603459128000000000000/4158583360817583356659 : ℝ))))
    (lo := ((-18014691428389/125000000000000 : ℝ))) (hi := ((-144105824180723/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((532282000283584999184133/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((77246710000000000000000/532282000283584999184133 : ℝ))) * ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ ((-7724671/1000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((4158583360817583356659/78125000000000000000 : ℝ))), hE4]
    have hnum : ((-75432391/9765625 : ℝ)) ≤ (-((603459128000000000000/4158583360817583356659 : ℝ))) * ((4158583360817583356659/78125000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((77246710000000000000000/532282000283584999184133 : ℝ))) (lo := ((18014690928389/125000000000000 : ℝ))) (hi := ((18014691428389/125000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-18014691428389/125000000000000 : ℝ)) ≤ Real.arctan (-((77246710000000000000000/532282000283584999184133 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((603459128000000000000/4158583360817583356659 : ℝ))) (lo := ((144105824180723/1000000000000000 : ℝ))) (hi := ((144105828180723/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((603459128000000000000/4158583360817583356659 : ℝ))) ≤ ((-144105824180723/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t14_delta : ((16887434029134686/95367431640625 : ℝ)) ≤ deltaY 2 2 2 2 (2 * hminus) (2 * hminus) ∧ deltaY 2 2 2 2 (2 * hminus) (2 * hminus) ≤ ((708354684284159/4000000000000 : ℝ)) := by
  have hE : deltaY 2 2 2 2 (2 * hminus) (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t14 : ((108254022870072161923/100000000000000000000 : ℝ)) ≤ dihY 2 2 2 2 (2 * hminus) (2 * hminus) ∧ dihY 2 2 2 2 (2 * hminus) (2 * hminus) ≤ ((216518767490720123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t14_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((5391959202067343/190734863281250 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((452354684284159/16000000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((5391959202067343/190734863281250 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((452354684284159/16000000000000 : ℝ)) := by
      have hf := ztgcHM_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 2 2 2 (2 * hminus) (2 * hminus) = ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((270198944466154976/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/250000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 2 (2 * hminus) (2 * hminus)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((532282000283584999184133/10000000000000000000000 : ℝ)) ^ 2 ≤ ((270198944466154976/95367431640625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((708354684284159/250000000000 : ℝ)) ≤ ((4158583360817583356659/78125000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((452354684284159/16000000000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 2 (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 2 2 2 (2 * hminus) (2 * hminus)) (dlo := ((532282000283584999184133/10000000000000000000000 : ℝ))) (dhi := ((4158583360817583356659/78125000000000000000 : ℝ)))
    (ulo := (-((282721677677599375000000/532282000283584999184133 : ℝ)))) (uhi := (-((116239288903514931200/218872808464083334561 : ℝ))))
    (lo := ((-19530243883767/40000000000000 : ℝ))) (hi := ((-30512655646331/62500000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((532282000283584999184133/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((282721677677599375000000/532282000283584999184133 : ℝ))) * ((532282000283584999184133/10000000000000000000000 : ℝ)) ≤ ((-452354684284159/16000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((4158583360817583356659/78125000000000000000 : ℝ))), hE4]
    have hnum : ((-5391959202067343/190734863281250 : ℝ)) ≤ (-((116239288903514931200/218872808464083334561 : ℝ))) * ((4158583360817583356659/78125000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((282721677677599375000000/532282000283584999184133 : ℝ))) (lo := ((19530243723767/40000000000000 : ℝ))) (hi := ((19530243883767/40000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-19530243883767/40000000000000 : ℝ)) ≤ Real.arctan (-((282721677677599375000000/532282000283584999184133 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((116239288903514931200/218872808464083334561 : ℝ))) (lo := ((30512655646331/62500000000000 : ℝ))) (hi := ((30512655896331/62500000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((116239288903514931200/218872808464083334561 : ℝ))) ≤ ((-30512655646331/62500000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t15_delta : ((56825987/250000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ∧ deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ≤ ((2219811308/9765625 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 = ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((56825987/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2219811308/9765625 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t15 : ((115778844869647661923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ≤ ((231560833507112523847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t15_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 = ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((1379469530174723/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((526245359218722572/95367431640625 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((157664/125 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) ≤ ((3941632/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((15172326976/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1379469530174723/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((526245359218722572/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((742824212695246786561929/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2) ≤ ((371418986756111986384693/5000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((742824212695246786561929/10000000000000000000000 : ℝ)) ^ 2 ≤ ((1379469530174723/250000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((526245359218722572/95367431640625 : ℝ)) ≤ ((371418986756111986384693/5000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2))| ≤ ((317885218/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2) (dlo := ((742824212695246786561929/10000000000000000000000 : ℝ))) (dhi := ((371418986756111986384693/5000000000000000000000 : ℝ)))
    (ulo := (-((325514463232000000000000/742824212695246786561929 : ℝ)))) (uhi := (-((23250470000000000000000/53059855250873140912099 : ℝ))))
    (lo := ((-20650393854921/50000000000000 : ℝ))) (hi := ((-206496080129667/500000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((742824212695246786561929/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((325514463232000000000000/742824212695246786561929 : ℝ))) * ((742824212695246786561929/10000000000000000000000 : ℝ)) ≤ ((-317885218/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((371418986756111986384693/5000000000000000000000 : ℝ))), hE4]
    have hnum : ((-16275329/500000 : ℝ)) ≤ (-((23250470000000000000000/53059855250873140912099 : ℝ))) * ((371418986756111986384693/5000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((325514463232000000000000/742824212695246786561929 : ℝ))) (lo := ((20650393654921/50000000000000 : ℝ))) (hi := ((20650393854921/50000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-20650393854921/50000000000000 : ℝ)) ≤ Real.arctan (-((325514463232000000000000/742824212695246786561929 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((23250470000000000000000/53059855250873140912099 : ℝ))) (lo := ((206496080129667/500000000000000 : ℝ))) (hi := ((206496082129667/500000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((23250470000000000000000/53059855250873140912099 : ℝ))) ≤ ((-206496080129667/500000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t16_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t16 : ((158274604480857171923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((316552782986764583847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t16_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((-638330377601881/762939453125000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-638330377601881/762939453125000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
      have hf := ztgcHM_f10
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((5420357059985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((2710353909271079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((218306663888374772190337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((1066029919138303725130111/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((34954104726806895238239/500000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((34954104726806895238239/500000000000000000000 : ℝ)) ^ 2 ≤ ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| ≤ ((638330377601881/762939453125000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_pos_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2) (dlo := ((34954104726806895238239/500000000000000000000 : ℝ))) (dhi := ((699115058066134057367019/10000000000000000000000 : ℝ)))
    (ulo := ((33824403128750000000/2830425336300137884077 : ℝ))) (uhi := ((418336196265168732160/34954104726806895238239 : ℝ)))
    (lo := ((119497190136751/10000000000000000 : ℝ))) (hi := ((119675871389263/10000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((699115058066134057367019/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((33824403128750000000/2830425336300137884077 : ℝ)) * ((699115058066134057367019/10000000000000000000000 : ℝ)) ≤ ((6683702058241/8000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((34954104726806895238239/500000000000000000000 : ℝ))), hE4]
    have hnum : ((638330377601881/762939453125000 : ℝ)) ≤ ((418336196265168732160/34954104726806895238239 : ℝ)) * ((34954104726806895238239/500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((33824403128750000000/2830425336300137884077 : ℝ))) (lo := ((119497190136751/10000000000000000 : ℝ))) (hi := ((119497230136751/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : ((119497190136751/10000000000000000 : ℝ)) ≤ Real.arctan ((33824403128750000000/2830425336300137884077 : ℝ)) := htp.1
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((418336196265168732160/34954104726806895238239 : ℝ))) (lo := ((119675831389263/10000000000000000 : ℝ))) (hi := ((119675871389263/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : Real.arctan ((418336196265168732160/34954104726806895238239 : ℝ)) ≤ ((119675871389263/10000000000000000 : ℝ)) := htp.2
    exact hfin

theorem ztgcHM_t17_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ∧ deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t17 : ((103917101337874261923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ∧ dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ≤ ((207845085209607923847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t17_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((328880027472641/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((125467480094391899/3051757812500000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((328880027472641/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((125467480094391899/3051757812500000 : ℝ)) := by
      have hf := ztgcHM_f11
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((5420357059985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((2710353909271079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((218306663888374772190337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((1066029919138303725130111/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((34954104726806895238239/500000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((34954104726806895238239/500000000000000000000 : ℝ)) ^ 2 ≤ ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((125467480094391899/3051757812500000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2) (dlo := ((34954104726806895238239/500000000000000000000 : ℝ))) (dhi := ((699115058066134057367019/10000000000000000000000 : ℝ)))
    (ulo := (-((20556591938665168732160/34954104726806895238239 : ℝ)))) (uhi := (-((21636843912673750000000/36795529371901792493001 : ℝ))))
    (lo := ((-265812656208077/500000000000000 : ℝ))) (hi := ((-531570901746857/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((34954104726806895238239/500000000000000000000 : ℝ))), hE4]
    have hnum : (-((20556591938665168732160/34954104726806895238239 : ℝ))) * ((34954104726806895238239/500000000000000000000 : ℝ)) ≤ ((-125467480094391899/3051757812500000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((699115058066134057367019/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-328880027472641/8000000000000 : ℝ)) ≤ (-((21636843912673750000000/36795529371901792493001 : ℝ))) * ((699115058066134057367019/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((20556591938665168732160/34954104726806895238239 : ℝ))) (lo := ((265812654208077/500000000000000 : ℝ))) (hi := ((265812656208077/500000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-265812656208077/500000000000000 : ℝ)) ≤ Real.arctan (-((20556591938665168732160/34954104726806895238239 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((21636843912673750000000/36795529371901792493001 : ℝ))) (lo := ((531570901746857/1000000000000000 : ℝ))) (hi := ((531570905746857/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((21636843912673750000000/36795529371901792493001 : ℝ))) ≤ ((-531570901746857/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t18_delta : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((-3650129975773/30517578125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/1000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  have hp4 : ((-56201051236976881/381469726562500 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
  have hp5 : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f12
    constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
  exact hp5

theorem ztgcHM_t18 : ((110252750616545361923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ ((220510749315028723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t18_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/4000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((3650129975773/122070312500 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    exact hp4
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((3314273926065743134310829686999/625000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((316094440315200000133914599787959/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((-865327585895733036757/298023223876953125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-2903439703632953407/1000000000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    have hp6 : ((-13323448840036601566947529/3725290298461914062500 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-14305247419799561436289/4000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp5.1, hp5.2, hf.1, hf.2]
    have hp7 : ((3314273926065743134310829686999/625000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((316094440315200000133914599787959/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcHM_f12
      constructor <;> nlinarith [hp6.1, hp6.2, hf.1, hf.2]
    exact hp7
  have hsA : ((364102948048334051587563/5000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus)) ≤ ((728229683010352682282123/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((364102948048334051587563/5000000000000000000000 : ℝ)) ^ 2 ≤ ((3314273926065743134310829686999/625000000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((316094440315200000133914599787959/59604644775390625000000000000 : ℝ)) ≤ ((728229683010352682282123/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus)) (dlo := ((364102948048334051587563/5000000000000000000000 : ℝ))) (dhi := ((728229683010352682282123/10000000000000000000000 : ℝ)))
    (ulo := (-((184159604693325843660800/364102948048334051587563 : ℝ)))) (uhi := (-((28331326829723125000000/56017667923873283252471 : ℝ))))
    (lo := ((-468268819629443/1000000000000000 : ℝ))) (hi := ((-468242581219753/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((364102948048334051587563/5000000000000000000000 : ℝ))), hE4]
    have hnum : (-((184159604693325843660800/364102948048334051587563 : ℝ))) * ((364102948048334051587563/5000000000000000000000 : ℝ)) ≤ ((-56201051236976881/1525878906250000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((728229683010352682282123/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-589291598058241/16000000000000 : ℝ)) ≤ (-((28331326829723125000000/56017667923873283252471 : ℝ))) * ((728229683010352682282123/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((184159604693325843660800/364102948048334051587563 : ℝ))) (lo := ((468268815629443/1000000000000000 : ℝ))) (hi := ((468268819629443/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-468268819629443/1000000000000000 : ℝ)) ≤ Real.arctan (-((184159604693325843660800/364102948048334051587563 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((28331326829723125000000/56017667923873283252471 : ℝ))) (lo := ((468242581219753/1000000000000000 : ℝ))) (hi := ((468242585219753/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((28331326829723125000000/56017667923873283252471 : ℝ))) ≤ ((-468242581219753/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t19_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ∧ deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t19 : ((158274604480857171923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ∧ dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ≤ ((316552782986764583847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t19_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((-638330377601881/762939453125000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-638330377601881/762939453125000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
      have hf := ztgcHM_f10
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((5420357059985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((2710353909271079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((218306663888374772190337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((1066029919138303725130111/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((34954104726806895238239/500000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((34954104726806895238239/500000000000000000000 : ℝ)) ^ 2 ≤ ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| ≤ ((638330377601881/762939453125000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_pos_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2) (dlo := ((34954104726806895238239/500000000000000000000 : ℝ))) (dhi := ((699115058066134057367019/10000000000000000000000 : ℝ)))
    (ulo := ((33824403128750000000/2830425336300137884077 : ℝ))) (uhi := ((418336196265168732160/34954104726806895238239 : ℝ)))
    (lo := ((119497190136751/10000000000000000 : ℝ))) (hi := ((119675871389263/10000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((699115058066134057367019/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((33824403128750000000/2830425336300137884077 : ℝ)) * ((699115058066134057367019/10000000000000000000000 : ℝ)) ≤ ((6683702058241/8000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((34954104726806895238239/500000000000000000000 : ℝ))), hE4]
    have hnum : ((638330377601881/762939453125000 : ℝ)) ≤ ((418336196265168732160/34954104726806895238239 : ℝ)) * ((34954104726806895238239/500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((33824403128750000000/2830425336300137884077 : ℝ))) (lo := ((119497190136751/10000000000000000 : ℝ))) (hi := ((119497230136751/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : ((119497190136751/10000000000000000 : ℝ)) ≤ Real.arctan ((33824403128750000000/2830425336300137884077 : ℝ)) := htp.1
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((418336196265168732160/34954104726806895238239 : ℝ))) (lo := ((119675831389263/10000000000000000 : ℝ))) (hi := ((119675871389263/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : Real.arctan ((418336196265168732160/34954104726806895238239 : ℝ)) ≤ ((119675871389263/10000000000000000 : ℝ)) := htp.2
    exact hfin

theorem ztgcHM_t20_delta : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ∧ deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((-3650129975773/30517578125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/1000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  have hp4 : ((-56201051236976881/381469726562500 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
  have hp5 : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f12
    constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
  exact hp5

theorem ztgcHM_t20 : ((110252750616545361923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ∧ dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((220510749315028723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t20_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/4000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((3650129975773/122070312500 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    exact hp4
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((3314273926065743134310829686999/625000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((316094440315200000133914599787959/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((-865327585895733036757/298023223876953125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-2903439703632953407/1000000000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    have hp6 : ((-13323448840036601566947529/3725290298461914062500 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-14305247419799561436289/4000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp5.1, hp5.2, hf.1, hf.2]
    have hp7 : ((3314273926065743134310829686999/625000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((316094440315200000133914599787959/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcHM_f12
      constructor <;> nlinarith [hp6.1, hp6.2, hf.1, hf.2]
    exact hp7
  have hsA : ((364102948048334051587563/5000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2) ≤ ((728229683010352682282123/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((364102948048334051587563/5000000000000000000000 : ℝ)) ^ 2 ≤ ((3314273926065743134310829686999/625000000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((316094440315200000133914599787959/59604644775390625000000000000 : ℝ)) ≤ ((728229683010352682282123/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2) (dlo := ((364102948048334051587563/5000000000000000000000 : ℝ))) (dhi := ((728229683010352682282123/10000000000000000000000 : ℝ)))
    (ulo := (-((184159604693325843660800/364102948048334051587563 : ℝ)))) (uhi := (-((28331326829723125000000/56017667923873283252471 : ℝ))))
    (lo := ((-468268819629443/1000000000000000 : ℝ))) (hi := ((-468242581219753/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((364102948048334051587563/5000000000000000000000 : ℝ))), hE4]
    have hnum : (-((184159604693325843660800/364102948048334051587563 : ℝ))) * ((364102948048334051587563/5000000000000000000000 : ℝ)) ≤ ((-56201051236976881/1525878906250000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((728229683010352682282123/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-589291598058241/16000000000000 : ℝ)) ≤ (-((28331326829723125000000/56017667923873283252471 : ℝ))) * ((728229683010352682282123/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((184159604693325843660800/364102948048334051587563 : ℝ))) (lo := ((468268815629443/1000000000000000 : ℝ))) (hi := ((468268819629443/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-468268819629443/1000000000000000 : ℝ)) ≤ Real.arctan (-((184159604693325843660800/364102948048334051587563 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((28331326829723125000000/56017667923873283252471 : ℝ))) (lo := ((468242581219753/1000000000000000 : ℝ))) (hi := ((468242585219753/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((28331326829723125000000/56017667923873283252471 : ℝ))) ≤ ((-468242581219753/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t21_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t21 : ((103917101337874261923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((207845085209607923847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t21_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((328880027472641/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((125467480094391899/3051757812500000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((328880027472641/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((125467480094391899/3051757812500000 : ℝ)) := by
      have hf := ztgcHM_f11
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((5420357059985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((2710353909271079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((218306663888374772190337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((1066029919138303725130111/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((34954104726806895238239/500000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus)) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((34954104726806895238239/500000000000000000000 : ℝ)) ^ 2 ≤ ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((125467480094391899/3051757812500000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus)) (dlo := ((34954104726806895238239/500000000000000000000 : ℝ))) (dhi := ((699115058066134057367019/10000000000000000000000 : ℝ)))
    (ulo := (-((20556591938665168732160/34954104726806895238239 : ℝ)))) (uhi := (-((21636843912673750000000/36795529371901792493001 : ℝ))))
    (lo := ((-265812656208077/500000000000000 : ℝ))) (hi := ((-531570901746857/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((34954104726806895238239/500000000000000000000 : ℝ))), hE4]
    have hnum : (-((20556591938665168732160/34954104726806895238239 : ℝ))) * ((34954104726806895238239/500000000000000000000 : ℝ)) ≤ ((-125467480094391899/3051757812500000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((699115058066134057367019/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-328880027472641/8000000000000 : ℝ)) ≤ (-((21636843912673750000000/36795529371901792493001 : ℝ))) * ((699115058066134057367019/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((20556591938665168732160/34954104726806895238239 : ℝ))) (lo := ((265812654208077/500000000000000 : ℝ))) (hi := ((265812656208077/500000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-265812656208077/500000000000000 : ℝ)) ≤ Real.arctan (-((20556591938665168732160/34954104726806895238239 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((21636843912673750000000/36795529371901792493001 : ℝ))) (lo := ((531570901746857/1000000000000000 : ℝ))) (hi := ((531570905746857/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((21636843912673750000000/36795529371901792493001 : ℝ))) ≤ ((-531570901746857/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t22_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ∧ deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t22 : ((158274604480857171923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ∧ dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ≤ ((316552782986764583847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t22_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((-638330377601881/762939453125000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-638330377601881/762939453125000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
      have hf := ztgcHM_f10
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((5420357059985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((2710353909271079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((218306663888374772190337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((1066029919138303725130111/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((34954104726806895238239/500000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((34954104726806895238239/500000000000000000000 : ℝ)) ^ 2 ≤ ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((638330377601881/762939453125000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_pos_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2) (dlo := ((34954104726806895238239/500000000000000000000 : ℝ))) (dhi := ((699115058066134057367019/10000000000000000000000 : ℝ)))
    (ulo := ((33824403128750000000/2830425336300137884077 : ℝ))) (uhi := ((418336196265168732160/34954104726806895238239 : ℝ)))
    (lo := ((119497190136751/10000000000000000 : ℝ))) (hi := ((119675871389263/10000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((699115058066134057367019/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((33824403128750000000/2830425336300137884077 : ℝ)) * ((699115058066134057367019/10000000000000000000000 : ℝ)) ≤ ((6683702058241/8000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((34954104726806895238239/500000000000000000000 : ℝ))), hE4]
    have hnum : ((638330377601881/762939453125000 : ℝ)) ≤ ((418336196265168732160/34954104726806895238239 : ℝ)) * ((34954104726806895238239/500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((33824403128750000000/2830425336300137884077 : ℝ))) (lo := ((119497190136751/10000000000000000 : ℝ))) (hi := ((119497230136751/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : ((119497190136751/10000000000000000 : ℝ)) ≤ Real.arctan ((33824403128750000000/2830425336300137884077 : ℝ)) := htp.1
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((418336196265168732160/34954104726806895238239 : ℝ))) (lo := ((119675831389263/10000000000000000 : ℝ))) (hi := ((119675871389263/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : Real.arctan ((418336196265168732160/34954104726806895238239 : ℝ)) ≤ ((119675871389263/10000000000000000 : ℝ)) := htp.2
    exact hfin

theorem ztgcHM_t23_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ∧ deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t23 : ((158274604480857171923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ∧ dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((316552782986764583847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t23_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((-638330377601881/762939453125000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-638330377601881/762939453125000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
      have hf := ztgcHM_f10
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((5420357059985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((2710353909271079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((218306663888374772190337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((1066029919138303725130111/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((34954104726806895238239/500000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus)) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((34954104726806895238239/500000000000000000000 : ℝ)) ^ 2 ≤ ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) ≤ ((699115058066134057367019/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((638330377601881/762939453125000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_pos_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus)) (dlo := ((34954104726806895238239/500000000000000000000 : ℝ))) (dhi := ((699115058066134057367019/10000000000000000000000 : ℝ)))
    (ulo := ((33824403128750000000/2830425336300137884077 : ℝ))) (uhi := ((418336196265168732160/34954104726806895238239 : ℝ)))
    (lo := ((119497190136751/10000000000000000 : ℝ))) (hi := ((119675871389263/10000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((699115058066134057367019/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((33824403128750000000/2830425336300137884077 : ℝ)) * ((699115058066134057367019/10000000000000000000000 : ℝ)) ≤ ((6683702058241/8000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((34954104726806895238239/500000000000000000000 : ℝ))), hE4]
    have hnum : ((638330377601881/762939453125000 : ℝ)) ≤ ((418336196265168732160/34954104726806895238239 : ℝ)) * ((34954104726806895238239/500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((33824403128750000000/2830425336300137884077 : ℝ))) (lo := ((119497190136751/10000000000000000 : ℝ))) (hi := ((119497230136751/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : ((119497190136751/10000000000000000 : ℝ)) ≤ Real.arctan ((33824403128750000000/2830425336300137884077 : ℝ)) := htp.1
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((418336196265168732160/34954104726806895238239 : ℝ))) (lo := ((119675831389263/10000000000000000 : ℝ))) (hi := ((119675871389263/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hfin : Real.arctan ((418336196265168732160/34954104726806895238239 : ℝ)) ≤ ((119675871389263/10000000000000000 : ℝ)) := htp.2
    exact hfin

theorem ztgcHM_t24_delta : ((56825987/250000 : ℝ)) ≤ deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) ∧ deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) ≤ ((2219811308/9765625 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) = ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((56825987/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2219811308/9765625 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t24 : ((115778844869647661923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) ≤ ((231560833507112523847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t24_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) = ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((1379469530174723/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((526245359218722572/95367431640625 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((157664/125 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) ≤ ((3941632/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((15172326976/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1379469530174723/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((526245359218722572/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((742824212695246786561929/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus)) ≤ ((371418986756111986384693/5000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((742824212695246786561929/10000000000000000000000 : ℝ)) ^ 2 ≤ ((1379469530174723/250000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((526245359218722572/95367431640625 : ℝ)) ≤ ((371418986756111986384693/5000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((317885218/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus)) (dlo := ((742824212695246786561929/10000000000000000000000 : ℝ))) (dhi := ((371418986756111986384693/5000000000000000000000 : ℝ)))
    (ulo := (-((325514463232000000000000/742824212695246786561929 : ℝ)))) (uhi := (-((23250470000000000000000/53059855250873140912099 : ℝ))))
    (lo := ((-20650393854921/50000000000000 : ℝ))) (hi := ((-206496080129667/500000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((742824212695246786561929/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((325514463232000000000000/742824212695246786561929 : ℝ))) * ((742824212695246786561929/10000000000000000000000 : ℝ)) ≤ ((-317885218/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((371418986756111986384693/5000000000000000000000 : ℝ))), hE4]
    have hnum : ((-16275329/500000 : ℝ)) ≤ (-((23250470000000000000000/53059855250873140912099 : ℝ))) * ((371418986756111986384693/5000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((325514463232000000000000/742824212695246786561929 : ℝ))) (lo := ((20650393654921/50000000000000 : ℝ))) (hi := ((20650393854921/50000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-20650393854921/50000000000000 : ℝ)) ≤ Real.arctan (-((325514463232000000000000/742824212695246786561929 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((23250470000000000000000/53059855250873140912099 : ℝ))) (lo := ((206496080129667/500000000000000 : ℝ))) (hi := ((206496082129667/500000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((23250470000000000000000/53059855250873140912099 : ℝ))) ≤ ((-206496080129667/500000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t25_delta : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((-3650129975773/30517578125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/1000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  have hp4 : ((-56201051236976881/381469726562500 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
  have hp5 : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f12
    constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
  exact hp5

theorem ztgcHM_t25 : ((137508956889747561923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((275021417366413923847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t25_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((1831146108781639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1831146108781639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((136528486434344232134231/39062500000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/381469726562500000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((136528486434344232134231/39062500000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f12
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((147799045280427954571773/2500000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2) ≤ ((295605346419088346123483/5000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((147799045280427954571773/2500000000000000000000 : ℝ)) ^ 2 ≤ ((136528486434344232134231/39062500000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((1333351450451419536331151/381469726562500000000 : ℝ)) ≤ ((295605346419088346123483/5000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2) (dlo := ((147799045280427954571773/2500000000000000000000 : ℝ))) (dhi := ((295605346419088346123483/5000000000000000000000 : ℝ)))
    (ulo := (-((29300308548506224000000/147799045280427954571773 : ℝ)))) (uhi := (-((4507436575462496000000/22738872801468334317191 : ℝ))))
    (lo := ((-195706756897421/1000000000000000 : ℝ))) (hi := ((-195689240962827/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((147799045280427954571773/2500000000000000000000 : ℝ))), hE4]
    have hnum : (-((29300308548506224000000/147799045280427954571773 : ℝ))) * ((147799045280427954571773/2500000000000000000000 : ℝ)) ≤ ((-1831269284281639/156250000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((295605346419088346123483/5000000000000000000000 : ℝ))), hE4]
    have hnum : ((-1831146108781639/156250000000000 : ℝ)) ≤ (-((4507436575462496000000/22738872801468334317191 : ℝ))) * ((295605346419088346123483/5000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((29300308548506224000000/147799045280427954571773 : ℝ))) (lo := ((195706752897421/1000000000000000 : ℝ))) (hi := ((195706756897421/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-195706756897421/1000000000000000 : ℝ)) ≤ Real.arctan (-((29300308548506224000000/147799045280427954571773 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((4507436575462496000000/22738872801468334317191 : ℝ))) (lo := ((195689240962827/1000000000000000 : ℝ))) (hi := ((195689244962827/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((4507436575462496000000/22738872801468334317191 : ℝ))) ≤ ((-195689240962827/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t26_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t26 : ((75775820509791704769/80000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ ((47361499785220465481/50000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t26_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((40825987/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((398702827/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((40825987/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((398702827/9765625 : ℝ)) := by
      have hf := ztgcHM_f13
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((7145173024/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/15625 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((8992943571985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((283775966931657032784567/5000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/78125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((1228867890169579548417611/381469726562500000000 : ℝ)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((398702827/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) (dlo := ((283775966931657032784567/5000000000000000000000 : ℝ))) (dhi := ((141893521884566521742673/2500000000000000000000 : ℝ)))
    (ulo := (-((204135847424000000000000/283775966931657032784567 : ℝ)))) (uhi := (-((102064967500000000000000/141893521884566521742673 : ℝ))))
    (lo := ((-249439427769000123847/400000000000000000000 : ℝ))) (hi := ((-124713266418097461923/200000000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((283775966931657032784567/5000000000000000000000 : ℝ))), hE4]
    have hnum : (-((204135847424000000000000/283775966931657032784567 : ℝ))) * ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ ((-398702827/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((141893521884566521742673/2500000000000000000000 : ℝ))), hE4]
    have hnum : ((-40825987/1000000 : ℝ)) ≤ (-((102064967500000000000000/141893521884566521742673 : ℝ))) * ((141893521884566521742673/2500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have hshift : Real.arctan (-((204135847424000000000000/283775966931657032784567 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((79640119507657032784567/487911814355657032784567 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((204135847424000000000000/283775966931657032784567 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((79640119507657032784567/487911814355657032784567 : ℝ))) (lo := ((40449898493737/250000000000000 : ℝ))) (hi := ((40449899493737/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : ((-249439427769000123847/400000000000000000000 : ℝ)) ≤ Real.arctan (-((204135847424000000000000/283775966931657032784567 : ℝ))) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin
  · have hshift : Real.arctan (-((102064967500000000000000/141893521884566521742673 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((39828554384566521742673/243958489384566521742673 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((102064967500000000000000/141893521884566521742673 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((39828554384566521742673/243958489384566521742673 : ℝ))) (lo := ((161831827306961/1000000000000000 : ℝ))) (hi := ((161831831306961/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : Real.arctan (-((102064967500000000000000/141893521884566521742673 : ℝ))) ≤ ((-124713266418097461923/200000000000000000000 : ℝ)) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin

theorem ztgcHM_t27_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ deltaY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t27 : ((75775820509791704769/80000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((47361499785220465481/50000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t27_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((40825987/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((398702827/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((40825987/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((398702827/9765625 : ℝ)) := by
      have hf := ztgcHM_f13
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((7145173024/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/15625 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((8992943571985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((283775966931657032784567/5000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/78125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((1228867890169579548417611/381469726562500000000 : ℝ)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((398702827/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) (dlo := ((283775966931657032784567/5000000000000000000000 : ℝ))) (dhi := ((141893521884566521742673/2500000000000000000000 : ℝ)))
    (ulo := (-((204135847424000000000000/283775966931657032784567 : ℝ)))) (uhi := (-((102064967500000000000000/141893521884566521742673 : ℝ))))
    (lo := ((-249439427769000123847/400000000000000000000 : ℝ))) (hi := ((-124713266418097461923/200000000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((283775966931657032784567/5000000000000000000000 : ℝ))), hE4]
    have hnum : (-((204135847424000000000000/283775966931657032784567 : ℝ))) * ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ ((-398702827/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((141893521884566521742673/2500000000000000000000 : ℝ))), hE4]
    have hnum : ((-40825987/1000000 : ℝ)) ≤ (-((102064967500000000000000/141893521884566521742673 : ℝ))) * ((141893521884566521742673/2500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have hshift : Real.arctan (-((204135847424000000000000/283775966931657032784567 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((79640119507657032784567/487911814355657032784567 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((204135847424000000000000/283775966931657032784567 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((79640119507657032784567/487911814355657032784567 : ℝ))) (lo := ((40449898493737/250000000000000 : ℝ))) (hi := ((40449899493737/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : ((-249439427769000123847/400000000000000000000 : ℝ)) ≤ Real.arctan (-((204135847424000000000000/283775966931657032784567 : ℝ))) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin
  · have hshift : Real.arctan (-((102064967500000000000000/141893521884566521742673 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((39828554384566521742673/243958489384566521742673 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((102064967500000000000000/141893521884566521742673 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((39828554384566521742673/243958489384566521742673 : ℝ))) (lo := ((161831827306961/1000000000000000 : ℝ))) (hi := ((161831831306961/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : Real.arctan (-((102064967500000000000000/141893521884566521742673 : ℝ))) ≤ ((-124713266418097461923/200000000000000000000 : ℝ)) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin

theorem ztgcHM_t28_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t28 : ((122759189454140761923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ ((245527054662685923847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t28_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((324468456887041/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((61893502620438137/3051757812500000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((324468456887041/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((61893502620438137/3051757812500000 : ℝ)) := by
      have hf := ztgcHM_f14
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((7145173024/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/15625 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((8992943571985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((283775966931657032784567/5000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/78125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((1228867890169579548417611/381469726562500000000 : ℝ)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((61893502620438137/3051757812500000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) (dlo := ((283775966931657032784567/5000000000000000000000 : ℝ))) (dhi := ((141893521884566521742673/2500000000000000000000 : ℝ)))
    (ulo := (-((9218755881211440332800/25797815175605184798597 : ℝ)))) (uhi := (-((50698196388600156250000/141893521884566521742673 : ℝ))))
    (lo := ((-343204431253489/1000000000000000 : ℝ))) (hi := ((-343161054481467/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((283775966931657032784567/5000000000000000000000 : ℝ))), hE4]
    have hnum : (-((9218755881211440332800/25797815175605184798597 : ℝ))) * ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ ((-61893502620438137/3051757812500000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((141893521884566521742673/2500000000000000000000 : ℝ))), hE4]
    have hnum : ((-324468456887041/16000000000000 : ℝ)) ≤ (-((50698196388600156250000/141893521884566521742673 : ℝ))) * ((141893521884566521742673/2500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((9218755881211440332800/25797815175605184798597 : ℝ))) (lo := ((343204427253489/1000000000000000 : ℝ))) (hi := ((343204431253489/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-343204431253489/1000000000000000 : ℝ)) ≤ Real.arctan (-((9218755881211440332800/25797815175605184798597 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((50698196388600156250000/141893521884566521742673 : ℝ))) (lo := ((343161054481467/1000000000000000 : ℝ))) (hi := ((343161058481467/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((50698196388600156250000/141893521884566521742673 : ℝ))) ≤ ((-343161054481467/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t29_delta : ((56825987/250000 : ℝ)) ≤ deltaY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ deltaY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((2219811308/9765625 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) = ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((56825987/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2219811308/9765625 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t29 : ((131145931161404061923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((262292379392363923847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t29_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) := by
    unfold deltaX4; ring
  have h4 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    exact hp0
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) = ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((56825987/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((35516980928/9765625 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((56825987/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((35516980928/9765625 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((1507660265263339733229/25000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) ≤ ((301535190910658190609123/5000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((1507660265263339733229/25000000000000000000 : ℝ)) ^ 2 ≤ ((56825987/15625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((35516980928/9765625 : ℝ)) ≤ ((301535190910658190609123/5000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((16/1 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) (dlo := ((1507660265263339733229/25000000000000000000 : ℝ))) (dhi := ((301535190910658190609123/5000000000000000000000 : ℝ)))
    (ulo := (-((400000000000000000000/1507660265263339733229 : ℝ)))) (uhi := (-((80000000000000000000000/301535190910658190609123 : ℝ))))
    (lo := ((-32417126772607/125000000000000 : ℝ))) (hi := ((-259334430833077/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((1507660265263339733229/25000000000000000000 : ℝ))), hE4]
    have hnum : (-((400000000000000000000/1507660265263339733229 : ℝ))) * ((1507660265263339733229/25000000000000000000 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((301535190910658190609123/5000000000000000000000 : ℝ))), hE4]
    have hnum : ((-16/1 : ℝ)) ≤ (-((80000000000000000000000/301535190910658190609123 : ℝ))) * ((301535190910658190609123/5000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((400000000000000000000/1507660265263339733229 : ℝ))) (lo := ((32417126272607/125000000000000 : ℝ))) (hi := ((32417126772607/125000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-32417126772607/125000000000000 : ℝ)) ≤ Real.arctan (-((400000000000000000000/1507660265263339733229 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((80000000000000000000000/301535190910658190609123 : ℝ))) (lo := ((259334430833077/1000000000000000 : ℝ))) (hi := ((259334434833077/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((80000000000000000000000/301535190910658190609123 : ℝ))) ≤ ((-259334430833077/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t30_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ deltaY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t30 : ((75775820509791704769/80000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ ((47361499785220465481/50000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t30_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((40825987/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((398702827/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((40825987/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((398702827/9765625 : ℝ)) := by
      have hf := ztgcHM_f13
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) = ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((7145173024/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/15625 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((8992943571985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((283775966931657032784567/5000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/78125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((1228867890169579548417611/381469726562500000000 : ℝ)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((398702827/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) (dlo := ((283775966931657032784567/5000000000000000000000 : ℝ))) (dhi := ((141893521884566521742673/2500000000000000000000 : ℝ)))
    (ulo := (-((204135847424000000000000/283775966931657032784567 : ℝ)))) (uhi := (-((102064967500000000000000/141893521884566521742673 : ℝ))))
    (lo := ((-249439427769000123847/400000000000000000000 : ℝ))) (hi := ((-124713266418097461923/200000000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((283775966931657032784567/5000000000000000000000 : ℝ))), hE4]
    have hnum : (-((204135847424000000000000/283775966931657032784567 : ℝ))) * ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ ((-398702827/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((141893521884566521742673/2500000000000000000000 : ℝ))), hE4]
    have hnum : ((-40825987/1000000 : ℝ)) ≤ (-((102064967500000000000000/141893521884566521742673 : ℝ))) * ((141893521884566521742673/2500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have hshift : Real.arctan (-((204135847424000000000000/283775966931657032784567 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((79640119507657032784567/487911814355657032784567 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((204135847424000000000000/283775966931657032784567 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((79640119507657032784567/487911814355657032784567 : ℝ))) (lo := ((40449898493737/250000000000000 : ℝ))) (hi := ((40449899493737/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : ((-249439427769000123847/400000000000000000000 : ℝ)) ≤ Real.arctan (-((204135847424000000000000/283775966931657032784567 : ℝ))) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin
  · have hshift : Real.arctan (-((102064967500000000000000/141893521884566521742673 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((39828554384566521742673/243958489384566521742673 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((102064967500000000000000/141893521884566521742673 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((39828554384566521742673/243958489384566521742673 : ℝ))) (lo := ((161831827306961/1000000000000000 : ℝ))) (hi := ((161831831306961/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : Real.arctan (-((102064967500000000000000/141893521884566521742673 : ℝ))) ≤ ((-124713266418097461923/200000000000000000000 : ℝ)) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin

theorem ztgcHM_t31_delta : ((56825987/250000 : ℝ)) ≤ deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((2219811308/9765625 : ℝ)) := by
  have hE : deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 = ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((56825987/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2219811308/9765625 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t31 : ((131145931161404061923/100000000000000000000 : ℝ)) ≤ dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((262292379392363923847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t31_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) := by
    unfold deltaX4; ring
  have h4 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    exact hp0
  have hE2 : 4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 = ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((56825987/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((35516980928/9765625 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((56825987/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((35516980928/9765625 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((1507660265263339733229/25000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) ≤ ((301535190910658190609123/5000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((1507660265263339733229/25000000000000000000 : ℝ)) ^ 2 ≤ ((56825987/15625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((35516980928/9765625 : ℝ)) ≤ ((301535190910658190609123/5000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((16/1 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) (dlo := ((1507660265263339733229/25000000000000000000 : ℝ))) (dhi := ((301535190910658190609123/5000000000000000000000 : ℝ)))
    (ulo := (-((400000000000000000000/1507660265263339733229 : ℝ)))) (uhi := (-((80000000000000000000000/301535190910658190609123 : ℝ))))
    (lo := ((-32417126772607/125000000000000 : ℝ))) (hi := ((-259334430833077/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((1507660265263339733229/25000000000000000000 : ℝ))), hE4]
    have hnum : (-((400000000000000000000/1507660265263339733229 : ℝ))) * ((1507660265263339733229/25000000000000000000 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((301535190910658190609123/5000000000000000000000 : ℝ))), hE4]
    have hnum : ((-16/1 : ℝ)) ≤ (-((80000000000000000000000/301535190910658190609123 : ℝ))) * ((301535190910658190609123/5000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((400000000000000000000/1507660265263339733229 : ℝ))) (lo := ((32417126272607/125000000000000 : ℝ))) (hi := ((32417126772607/125000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-32417126772607/125000000000000 : ℝ)) ≤ Real.arctan (-((400000000000000000000/1507660265263339733229 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((80000000000000000000000/301535190910658190609123 : ℝ))) (lo := ((259334430833077/1000000000000000 : ℝ))) (hi := ((259334434833077/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((80000000000000000000000/301535190910658190609123 : ℝ))) ≤ ((-259334430833077/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t32_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ deltaY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t32 : ((122759189454140761923/100000000000000000000 : ℝ)) ≤ dihY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ dihY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((245527054662685923847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t32_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((324468456887041/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((61893502620438137/3051757812500000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((324468456887041/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((61893502620438137/3051757812500000 : ℝ)) := by
      have hf := ztgcHM_f14
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((7145173024/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/15625 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((8992943571985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((283775966931657032784567/5000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/78125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((1228867890169579548417611/381469726562500000000 : ℝ)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((61893502620438137/3051757812500000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) (dlo := ((283775966931657032784567/5000000000000000000000 : ℝ))) (dhi := ((141893521884566521742673/2500000000000000000000 : ℝ)))
    (ulo := (-((9218755881211440332800/25797815175605184798597 : ℝ)))) (uhi := (-((50698196388600156250000/141893521884566521742673 : ℝ))))
    (lo := ((-343204431253489/1000000000000000 : ℝ))) (hi := ((-343161054481467/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((283775966931657032784567/5000000000000000000000 : ℝ))), hE4]
    have hnum : (-((9218755881211440332800/25797815175605184798597 : ℝ))) * ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ ((-61893502620438137/3051757812500000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((141893521884566521742673/2500000000000000000000 : ℝ))), hE4]
    have hnum : ((-324468456887041/16000000000000 : ℝ)) ≤ (-((50698196388600156250000/141893521884566521742673 : ℝ))) * ((141893521884566521742673/2500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((9218755881211440332800/25797815175605184798597 : ℝ))) (lo := ((343204427253489/1000000000000000 : ℝ))) (hi := ((343204431253489/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-343204431253489/1000000000000000 : ℝ)) ≤ Real.arctan (-((9218755881211440332800/25797815175605184798597 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((50698196388600156250000/141893521884566521742673 : ℝ))) (lo := ((343161054481467/1000000000000000 : ℝ))) (hi := ((343161058481467/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((50698196388600156250000/141893521884566521742673 : ℝ))) ≤ ((-343161054481467/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t33_delta : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ deltaY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ deltaY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
  have hE : deltaY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
    have hf := ztgcHM_f7
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
    have hf := ztgcHM_f8
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f9
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t33 : ((75775820509791704769/80000000000000000000 : ℝ)) ≤ dihY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ dihY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((47361499785220465481/50000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t33_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((40825987/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((398702827/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((40825987/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((398702827/9765625 : ℝ)) := by
      have hf := ztgcHM_f13
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((7145173024/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/15625 : ℝ)) := by
      have hf := ztgcHM_f7
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((8992943571985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/2441406250000 : ℝ)) := by
      have hf := ztgcHM_f8
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((251652498653295719514337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f9
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((283775966931657032784567/5000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/78125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((1228867890169579548417611/381469726562500000000 : ℝ)) ≤ ((141893521884566521742673/2500000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((398702827/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) (dlo := ((283775966931657032784567/5000000000000000000000 : ℝ))) (dhi := ((141893521884566521742673/2500000000000000000000 : ℝ)))
    (ulo := (-((204135847424000000000000/283775966931657032784567 : ℝ)))) (uhi := (-((102064967500000000000000/141893521884566521742673 : ℝ))))
    (lo := ((-249439427769000123847/400000000000000000000 : ℝ))) (hi := ((-124713266418097461923/200000000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((283775966931657032784567/5000000000000000000000 : ℝ))), hE4]
    have hnum : (-((204135847424000000000000/283775966931657032784567 : ℝ))) * ((283775966931657032784567/5000000000000000000000 : ℝ)) ≤ ((-398702827/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((141893521884566521742673/2500000000000000000000 : ℝ))), hE4]
    have hnum : ((-40825987/1000000 : ℝ)) ≤ (-((102064967500000000000000/141893521884566521742673 : ℝ))) * ((141893521884566521742673/2500000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have hshift : Real.arctan (-((204135847424000000000000/283775966931657032784567 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((79640119507657032784567/487911814355657032784567 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((204135847424000000000000/283775966931657032784567 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((79640119507657032784567/487911814355657032784567 : ℝ))) (lo := ((40449898493737/250000000000000 : ℝ))) (hi := ((40449899493737/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : ((-249439427769000123847/400000000000000000000 : ℝ)) ≤ Real.arctan (-((204135847424000000000000/283775966931657032784567 : ℝ))) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin
  · have hshift : Real.arctan (-((102064967500000000000000/141893521884566521742673 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((39828554384566521742673/243958489384566521742673 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((102064967500000000000000/141893521884566521742673 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((39828554384566521742673/243958489384566521742673 : ℝ))) (lo := ((161831827306961/1000000000000000 : ℝ))) (hi := ((161831831306961/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : Real.arctan (-((102064967500000000000000/141893521884566521742673 : ℝ))) ≤ ((-124713266418097461923/200000000000000000000 : ℝ)) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin

theorem ztgcHM_t34_delta : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ deltaY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ deltaY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
  have hE : deltaY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((-3650129975773/30517578125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/1000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  have hp4 : ((-56201051236976881/381469726562500 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/4000000000000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
  have hp5 : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
    have hf := ztgcHM_f12
    constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
  exact hp5

theorem ztgcHM_t34 : ((137508956889747561923/100000000000000000000 : ℝ)) ≤ dihY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ dihY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((275021417366413923847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t34_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((1831146108781639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1831146108781639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((136528486434344232134231/39062500000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/381469726562500000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((136528486434344232134231/39062500000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/381469726562500000000 : ℝ)) := by
      have hf := ztgcHM_f12
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((147799045280427954571773/2500000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((295605346419088346123483/5000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((147799045280427954571773/2500000000000000000000 : ℝ)) ^ 2 ≤ ((136528486434344232134231/39062500000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((1333351450451419536331151/381469726562500000000 : ℝ)) ≤ ((295605346419088346123483/5000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) (dlo := ((147799045280427954571773/2500000000000000000000 : ℝ))) (dhi := ((295605346419088346123483/5000000000000000000000 : ℝ)))
    (ulo := (-((29300308548506224000000/147799045280427954571773 : ℝ)))) (uhi := (-((4507436575462496000000/22738872801468334317191 : ℝ))))
    (lo := ((-195706756897421/1000000000000000 : ℝ))) (hi := ((-195689240962827/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((147799045280427954571773/2500000000000000000000 : ℝ))), hE4]
    have hnum : (-((29300308548506224000000/147799045280427954571773 : ℝ))) * ((147799045280427954571773/2500000000000000000000 : ℝ)) ≤ ((-1831269284281639/156250000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((295605346419088346123483/5000000000000000000000 : ℝ))), hE4]
    have hnum : ((-1831146108781639/156250000000000 : ℝ)) ≤ (-((4507436575462496000000/22738872801468334317191 : ℝ))) * ((295605346419088346123483/5000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((29300308548506224000000/147799045280427954571773 : ℝ))) (lo := ((195706752897421/1000000000000000 : ℝ))) (hi := ((195706756897421/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-195706756897421/1000000000000000 : ℝ)) ≤ Real.arctan (-((29300308548506224000000/147799045280427954571773 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((4507436575462496000000/22738872801468334317191 : ℝ))) (lo := ((195689240962827/1000000000000000 : ℝ))) (hi := ((195689244962827/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((4507436575462496000000/22738872801468334317191 : ℝ))) ≤ ((-195689240962827/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t35_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t35 : ((147891111982938951923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((295792839738049903847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t35_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((11348684879561863/1525878906250000 : ℝ)) ≤ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((59531543112959/8000000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((11348684879561863/1525878906250000 : ℝ)) ≤ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((59531543112959/8000000000000 : ℝ)) := by
      have hf := ztgcHM_f15
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((161516508470776491367707/2000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| ≤ ((59531543112959/8000000000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2) (dlo := ((161516508470776491367707/2000000000000000000000 : ℝ))) (dhi := ((807620947293149946485529/10000000000000000000000 : ℝ)))
    (ulo := (-((14882885778239750000000/161516508470776491367707 : ℝ)))) (uhi := (-((3233684401160722841600/35113954230136954195023 : ℝ))))
    (lo := ((-918852059655071/10000000000000000 : ℝ))) (hi := ((-918321291046471/10000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((161516508470776491367707/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((14882885778239750000000/161516508470776491367707 : ℝ))) * ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ ((-59531543112959/8000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((807620947293149946485529/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-11348684879561863/1525878906250000 : ℝ)) ≤ (-((3233684401160722841600/35113954230136954195023 : ℝ))) * ((807620947293149946485529/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((14882885778239750000000/161516508470776491367707 : ℝ))) (lo := ((918852019655071/10000000000000000 : ℝ))) (hi := ((918852059655071/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-918852059655071/10000000000000000 : ℝ)) ≤ Real.arctan (-((14882885778239750000000/161516508470776491367707 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((3233684401160722841600/35113954230136954195023 : ℝ))) (lo := ((918321291046471/10000000000000000 : ℝ))) (hi := ((918321331046471/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((3233684401160722841600/35113954230136954195023 : ℝ))) ≤ ((-918321291046471/10000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t36_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t36 : ((102192375318748461923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ ((204392586117475123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t36_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((395088966058241/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((395088966058241/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((161516508470776491367707/2000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) (dlo := ((161516508470776491367707/2000000000000000000000 : ℝ))) (dhi := ((807620947293149946485529/10000000000000000000000 : ℝ)))
    (ulo := (-((98776237431460674928640/161516508470776491367707 : ℝ)))) (uhi := (-((235958532046250000000/385867628902603892253 : ℝ))))
    (lo := ((-137218143151853/250000000000000 : ℝ))) (hi := ((-548833397207521/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((161516508470776491367707/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((98776237431460674928640/161516508470776491367707 : ℝ))) * ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ ((-37680144283851881/762939453125000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((807620947293149946485529/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-395088966058241/8000000000000 : ℝ)) ≤ (-((235958532046250000000/385867628902603892253 : ℝ))) * ((807620947293149946485529/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((98776237431460674928640/161516508470776491367707 : ℝ))) (lo := ((137218142151853/250000000000000 : ℝ))) (hi := ((137218143151853/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-137218143151853/250000000000000 : ℝ)) ≤ Real.arctan (-((98776237431460674928640/161516508470776491367707 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((235958532046250000000/385867628902603892253 : ℝ))) (lo := ((548833397207521/1000000000000000 : ℝ))) (hi := ((548833401207521/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((235958532046250000000/385867628902603892253 : ℝ))) ≤ ((-548833397207521/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t37_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t37 : ((102192375318748461923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((204392586117475123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t37_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((395088966058241/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((395088966058241/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((161516508470776491367707/2000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) (dlo := ((161516508470776491367707/2000000000000000000000 : ℝ))) (dhi := ((807620947293149946485529/10000000000000000000000 : ℝ)))
    (ulo := (-((98776237431460674928640/161516508470776491367707 : ℝ)))) (uhi := (-((235958532046250000000/385867628902603892253 : ℝ))))
    (lo := ((-137218143151853/250000000000000 : ℝ))) (hi := ((-548833397207521/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((161516508470776491367707/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((98776237431460674928640/161516508470776491367707 : ℝ))) * ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ ((-37680144283851881/762939453125000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((807620947293149946485529/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-395088966058241/8000000000000 : ℝ)) ≤ (-((235958532046250000000/385867628902603892253 : ℝ))) * ((807620947293149946485529/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((98776237431460674928640/161516508470776491367707 : ℝ))) (lo := ((137218142151853/250000000000000 : ℝ))) (hi := ((137218143151853/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-137218143151853/250000000000000 : ℝ)) ≤ Real.arctan (-((98776237431460674928640/161516508470776491367707 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((235958532046250000000/385867628902603892253 : ℝ))) (lo := ((548833397207521/1000000000000000 : ℝ))) (hi := ((548833401207521/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((235958532046250000000/385867628902603892253 : ℝ))) ≤ ((-548833397207521/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t38_delta : ((16275329/62500 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ ((2543081744/9765625 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 = ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by
    norm_num
  have hp1 : ((16275329/62500 : ℝ)) ≤ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2543081744/9765625 : ℝ)) := by
    have hf := ztgcHM_f5
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t38 : ((137220952814990661923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ ((274442689328030723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t38_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) := by
    unfold deltaX4; ring
  have h4 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    exact hp0
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 = ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((395088966058241/62500000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((602882308541630096/95367431640625 : ℝ)) := by
    have hp0 : ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) ∧ ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) := by
      norm_num
    have hp1 : ((315328/125 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) ≤ ((7883264/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((48550658/15625 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) ≤ ((30344653952/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((395088966058241/62500000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((602882308541630096/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((795073798102353201102573/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) ≤ ((159017976446146976287129/2000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((795073798102353201102573/10000000000000000000000 : ℝ)) ^ 2 ≤ ((395088966058241/62500000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((602882308541630096/95367431640625 : ℝ)) ≤ ((159017976446146976287129/2000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((16/1 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) (dlo := ((795073798102353201102573/10000000000000000000000 : ℝ))) (dhi := ((159017976446146976287129/2000000000000000000000 : ℝ)))
    (ulo := (-((160000000000000000000000/795073798102353201102573 : ℝ)))) (uhi := (-((32000000000000000000000/159017976446146976287129 : ℝ))))
    (lo := ((-19858679764499/100000000000000 : ℝ))) (hi := ((-198582881154743/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((795073798102353201102573/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((160000000000000000000000/795073798102353201102573 : ℝ))) * ((795073798102353201102573/10000000000000000000000 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((159017976446146976287129/2000000000000000000000 : ℝ))), hE4]
    have hnum : ((-16/1 : ℝ)) ≤ (-((32000000000000000000000/159017976446146976287129 : ℝ))) * ((159017976446146976287129/2000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((160000000000000000000000/795073798102353201102573 : ℝ))) (lo := ((19858679364499/100000000000000 : ℝ))) (hi := ((19858679764499/100000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-19858679764499/100000000000000 : ℝ)) ≤ Real.arctan (-((160000000000000000000000/795073798102353201102573 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((32000000000000000000000/159017976446146976287129 : ℝ))) (lo := ((198582881154743/1000000000000000 : ℝ))) (hi := ((198582885154743/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((32000000000000000000000/159017976446146976287129 : ℝ))) ≤ ((-198582881154743/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t39_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t39 : ((142667648658134061923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((285338562236501123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t39_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((1831146108781639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1831146108781639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((161516508470776491367707/2000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) (dlo := ((161516508470776491367707/2000000000000000000000 : ℝ))) (dhi := ((807620947293149946485529/10000000000000000000000 : ℝ)))
    (ulo := (-((23440246838804979200000/161516508470776491367707 : ℝ)))) (uhi := (-((9014873150924992000000/62124688253319226652733 : ℝ))))
    (lo := ((-36029959803389/250000000000000 : ℝ))) (hi := ((-144103516612391/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((161516508470776491367707/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((23440246838804979200000/161516508470776491367707 : ℝ))) * ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ ((-1831269284281639/156250000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((807620947293149946485529/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-1831146108781639/156250000000000 : ℝ)) ≤ (-((9014873150924992000000/62124688253319226652733 : ℝ))) * ((807620947293149946485529/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((23440246838804979200000/161516508470776491367707 : ℝ))) (lo := ((36029958803389/250000000000000 : ℝ))) (hi := ((36029959803389/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-36029959803389/250000000000000 : ℝ)) ≤ Real.arctan (-((23440246838804979200000/161516508470776491367707 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((9014873150924992000000/62124688253319226652733 : ℝ))) (lo := ((144103516612391/1000000000000000 : ℝ))) (hi := ((144103520612391/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((9014873150924992000000/62124688253319226652733 : ℝ))) ≤ ((-144103516612391/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t40_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t40 : ((102192375318748461923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ ((204392586117475123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t40_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((395088966058241/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((395088966058241/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((161516508470776491367707/2000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) (dlo := ((161516508470776491367707/2000000000000000000000 : ℝ))) (dhi := ((807620947293149946485529/10000000000000000000000 : ℝ)))
    (ulo := (-((98776237431460674928640/161516508470776491367707 : ℝ)))) (uhi := (-((235958532046250000000/385867628902603892253 : ℝ))))
    (lo := ((-137218143151853/250000000000000 : ℝ))) (hi := ((-548833397207521/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((161516508470776491367707/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((98776237431460674928640/161516508470776491367707 : ℝ))) * ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ ((-37680144283851881/762939453125000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((807620947293149946485529/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-395088966058241/8000000000000 : ℝ)) ≤ (-((235958532046250000000/385867628902603892253 : ℝ))) * ((807620947293149946485529/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((98776237431460674928640/161516508470776491367707 : ℝ))) (lo := ((137218142151853/250000000000000 : ℝ))) (hi := ((137218143151853/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-137218143151853/250000000000000 : ℝ)) ≤ Real.arctan (-((98776237431460674928640/161516508470776491367707 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((235958532046250000000/385867628902603892253 : ℝ))) (lo := ((548833397207521/1000000000000000 : ℝ))) (hi := ((548833401207521/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((235958532046250000000/385867628902603892253 : ℝ))) ≤ ((-548833397207521/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t41_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t41 : ((142667648658134061923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((285338562236501123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t41_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((1831146108781639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1831146108781639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
      have hf := ztgcHM_f2
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((161516508470776491367707/2000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) (dlo := ((161516508470776491367707/2000000000000000000000 : ℝ))) (dhi := ((807620947293149946485529/10000000000000000000000 : ℝ)))
    (ulo := (-((23440246838804979200000/161516508470776491367707 : ℝ)))) (uhi := (-((9014873150924992000000/62124688253319226652733 : ℝ))))
    (lo := ((-36029959803389/250000000000000 : ℝ))) (hi := ((-144103516612391/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((161516508470776491367707/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((23440246838804979200000/161516508470776491367707 : ℝ))) * ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ ((-1831269284281639/156250000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((807620947293149946485529/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-1831146108781639/156250000000000 : ℝ)) ≤ (-((9014873150924992000000/62124688253319226652733 : ℝ))) * ((807620947293149946485529/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((23440246838804979200000/161516508470776491367707 : ℝ))) (lo := ((36029958803389/250000000000000 : ℝ))) (hi := ((36029959803389/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-36029959803389/250000000000000 : ℝ)) ≤ Real.arctan (-((23440246838804979200000/161516508470776491367707 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((9014873150924992000000/62124688253319226652733 : ℝ))) (lo := ((144103516612391/1000000000000000 : ℝ))) (hi := ((144103520612391/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((9014873150924992000000/62124688253319226652733 : ℝ))) ≤ ((-144103516612391/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t42_delta : ((16275329/62500 : ℝ)) ≤ deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((2543081744/9765625 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) = ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by
    norm_num
  have hp1 : ((16275329/62500 : ℝ)) ≤ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2543081744/9765625 : ℝ)) := by
    have hf := ztgcHM_f5
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t42 : ((137220952814990661923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((274442689328030723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t42_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) := by
    unfold deltaX4; ring
  have h4 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    exact hp0
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) = ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((395088966058241/62500000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((602882308541630096/95367431640625 : ℝ)) := by
    have hp0 : ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) ∧ ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) := by
      norm_num
    have hp1 : ((315328/125 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) ≤ ((7883264/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((48550658/15625 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) ≤ ((30344653952/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((395088966058241/62500000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((602882308541630096/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((795073798102353201102573/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) ≤ ((159017976446146976287129/2000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((795073798102353201102573/10000000000000000000000 : ℝ)) ^ 2 ≤ ((395088966058241/62500000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((602882308541630096/95367431640625 : ℝ)) ≤ ((159017976446146976287129/2000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((16/1 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) (dlo := ((795073798102353201102573/10000000000000000000000 : ℝ))) (dhi := ((159017976446146976287129/2000000000000000000000 : ℝ)))
    (ulo := (-((160000000000000000000000/795073798102353201102573 : ℝ)))) (uhi := (-((32000000000000000000000/159017976446146976287129 : ℝ))))
    (lo := ((-19858679764499/100000000000000 : ℝ))) (hi := ((-198582881154743/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((795073798102353201102573/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((160000000000000000000000/795073798102353201102573 : ℝ))) * ((795073798102353201102573/10000000000000000000000 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((159017976446146976287129/2000000000000000000000 : ℝ))), hE4]
    have hnum : ((-16/1 : ℝ)) ≤ (-((32000000000000000000000/159017976446146976287129 : ℝ))) * ((159017976446146976287129/2000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((160000000000000000000000/795073798102353201102573 : ℝ))) (lo := ((19858679364499/100000000000000 : ℝ))) (hi := ((19858679764499/100000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-19858679764499/100000000000000 : ℝ)) ≤ Real.arctan (-((160000000000000000000000/795073798102353201102573 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((32000000000000000000000/159017976446146976287129 : ℝ))) (lo := ((198582881154743/1000000000000000 : ℝ))) (hi := ((198582885154743/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((32000000000000000000000/159017976446146976287129 : ℝ))) ≤ ((-198582881154743/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t43_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t43 : ((102192375318748461923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((204392586117475123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t43_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((395088966058241/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((395088966058241/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((161516508470776491367707/2000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) (dlo := ((161516508470776491367707/2000000000000000000000 : ℝ))) (dhi := ((807620947293149946485529/10000000000000000000000 : ℝ)))
    (ulo := (-((98776237431460674928640/161516508470776491367707 : ℝ)))) (uhi := (-((235958532046250000000/385867628902603892253 : ℝ))))
    (lo := ((-137218143151853/250000000000000 : ℝ))) (hi := ((-548833397207521/1000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((161516508470776491367707/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((98776237431460674928640/161516508470776491367707 : ℝ))) * ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ ((-37680144283851881/762939453125000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((807620947293149946485529/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-395088966058241/8000000000000 : ℝ)) ≤ (-((235958532046250000000/385867628902603892253 : ℝ))) * ((807620947293149946485529/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((98776237431460674928640/161516508470776491367707 : ℝ))) (lo := ((137218142151853/250000000000000 : ℝ))) (hi := ((137218143151853/250000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-137218143151853/250000000000000 : ℝ)) ≤ Real.arctan (-((98776237431460674928640/161516508470776491367707 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((235958532046250000000/385867628902603892253 : ℝ))) (lo := ((548833397207521/1000000000000000 : ℝ))) (hi := ((548833401207521/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((235958532046250000000/385867628902603892253 : ℝ))) ≤ ((-548833397207521/1000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t44_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t44 : ((147891111982938951923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((295792839738049903847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t44_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((11348684879561863/1525878906250000 : ℝ)) ≤ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((59531543112959/8000000000000 : ℝ)) := by
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by
      norm_num
    have hp1 : ((11348684879561863/1525878906250000 : ℝ)) ≤ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((59531543112959/8000000000000 : ℝ)) := by
      have hf := ztgcHM_f15
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((161516508470776491367707/2000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((807620947293149946485529/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((59531543112959/8000000000000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) (dlo := ((161516508470776491367707/2000000000000000000000 : ℝ))) (dhi := ((807620947293149946485529/10000000000000000000000 : ℝ)))
    (ulo := (-((14882885778239750000000/161516508470776491367707 : ℝ)))) (uhi := (-((3233684401160722841600/35113954230136954195023 : ℝ))))
    (lo := ((-918852059655071/10000000000000000 : ℝ))) (hi := ((-918321291046471/10000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((161516508470776491367707/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((14882885778239750000000/161516508470776491367707 : ℝ))) * ((161516508470776491367707/2000000000000000000000 : ℝ)) ≤ ((-59531543112959/8000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((807620947293149946485529/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-11348684879561863/1525878906250000 : ℝ)) ≤ (-((3233684401160722841600/35113954230136954195023 : ℝ))) * ((807620947293149946485529/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((14882885778239750000000/161516508470776491367707 : ℝ))) (lo := ((918852019655071/10000000000000000 : ℝ))) (hi := ((918852059655071/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-918852059655071/10000000000000000 : ℝ)) ≤ Real.arctan (-((14882885778239750000000/161516508470776491367707 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((3233684401160722841600/35113954230136954195023 : ℝ))) (lo := ((918321291046471/10000000000000000 : ℝ))) (hi := ((918321331046471/10000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((3233684401160722841600/35113954230136954195023 : ℝ))) ≤ ((-918321291046471/10000000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t45_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t45 : ((121618696107134461923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((243241018979273723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t45_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((131127670769861329099011/2000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) (dlo := ((131127670769861329099011/2000000000000000000000 : ℝ))) (dhi := ((655664209986645209330981/10000000000000000000000 : ℝ)))
    (ulo := (-((48551446323200000000000/131127670769861329099011 : ℝ)))) (uhi := (-((18673330000000000000000/50435708460511169948537 : ℝ))))
    (lo := ((-11081542647611/31250000000000 : ℝ))) (hi := ((-11080976028079/31250000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((131127670769861329099011/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((48551446323200000000000/131127670769861329099011 : ℝ))) * ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((655664209986645209330981/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/50435708460511169948537 : ℝ))) * ((655664209986645209330981/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((48551446323200000000000/131127670769861329099011 : ℝ))) (lo := ((11081542522611/31250000000000 : ℝ))) (hi := ((11081542647611/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-11081542647611/31250000000000 : ℝ)) ≤ Real.arctan (-((48551446323200000000000/131127670769861329099011 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/50435708460511169948537 : ℝ))) (lo := ((11080976028079/31250000000000 : ℝ))) (hi := ((11080976153079/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/50435708460511169948537 : ℝ))) ≤ ((-11080976028079/31250000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t46_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t46 : ((121618696107134461923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((243241018979273723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t46_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((131127670769861329099011/2000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) (dlo := ((131127670769861329099011/2000000000000000000000 : ℝ))) (dhi := ((655664209986645209330981/10000000000000000000000 : ℝ)))
    (ulo := (-((48551446323200000000000/131127670769861329099011 : ℝ)))) (uhi := (-((18673330000000000000000/50435708460511169948537 : ℝ))))
    (lo := ((-11081542647611/31250000000000 : ℝ))) (hi := ((-11080976028079/31250000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((131127670769861329099011/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((48551446323200000000000/131127670769861329099011 : ℝ))) * ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((655664209986645209330981/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/50435708460511169948537 : ℝ))) * ((655664209986645209330981/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((48551446323200000000000/131127670769861329099011 : ℝ))) (lo := ((11081542522611/31250000000000 : ℝ))) (hi := ((11081542647611/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-11081542647611/31250000000000 : ℝ)) ≤ Real.arctan (-((48551446323200000000000/131127670769861329099011 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/50435708460511169948537 : ℝ))) (lo := ((11080976028079/31250000000000 : ℝ))) (hi := ((11080976153079/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/50435708460511169948537 : ℝ))) ≤ ((-11080976028079/31250000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t47_delta : ((16275329/62500 : ℝ)) ≤ deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((2543081744/9765625 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) = ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by
    norm_num
  have hp1 : ((16275329/62500 : ℝ)) ≤ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2543081744/9765625 : ℝ)) := by
    have hf := ztgcHM_f5
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  exact hp1

theorem ztgcHM_t47 : ((73637804700160184769/80000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((46024693650039615481/50000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t47_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((12275329/250000 : ℝ)) ≤ ((16/1 : ℝ)) * (((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((479520436/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((12275329/250000 : ℝ)) ≤ ((16/1 : ℝ)) * (((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((479520436/9765625 : ℝ)) := by
      have hf := ztgcHM_f16
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) = ((2048/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((65101316/15625 : ℝ)) ≤ ((2048/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((40689307904/9765625 : ℝ)) := by
    have hp0 : ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) ∧ ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) := by
      norm_num
    have hp1 : ((65101316/15625 : ℝ)) ≤ ((2048/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((40689307904/9765625 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hsA : ((64548309161952690773499/1000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) ≤ ((645490909130621908485131/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((64548309161952690773499/1000000000000000000000 : ℝ)) ^ 2 ≤ ((65101316/15625 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((40689307904/9765625 : ℝ)) ≤ ((645490909130621908485131/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((479520436/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) (dlo := ((64548309161952690773499/1000000000000000000000 : ℝ))) (dhi := ((645490909130621908485131/10000000000000000000000 : ℝ)))
    (ulo := (-((49102892646400000000000/64548309161952690773499 : ℝ)))) (uhi := (-((44637560000000000000000/58680991739147446225921 : ℝ))))
    (lo := ((-260129506817157723847/400000000000000000000 : ℝ))) (hi := ((-130060490958820861923/200000000000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((64548309161952690773499/1000000000000000000000 : ℝ))), hE4]
    have hnum : (-((49102892646400000000000/64548309161952690773499 : ℝ))) * ((64548309161952690773499/1000000000000000000000 : ℝ)) ≤ ((-479520436/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((645490909130621908485131/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-12275329/250000 : ℝ)) ≤ (-((44637560000000000000000/58680991739147446225921 : ℝ))) * ((645490909130621908485131/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have hshift : Real.arctan (-((49102892646400000000000/64548309161952690773499 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((15445416515552690773499/113651201808352690773499 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((49102892646400000000000/64548309161952690773499 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((15445416515552690773499/113651201808352690773499 : ℝ))) (lo := ((67537198177277/500000000000000 : ℝ))) (hi := ((67537200177277/500000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : ((-260129506817157723847/400000000000000000000 : ℝ)) ≤ Real.arctan (-((49102892646400000000000/64548309161952690773499 : ℝ))) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin
  · have hshift : Real.arctan (-((44637560000000000000000/58680991739147446225921 : ℝ))) = -(Real.pi / 4 + Real.arctan (-((14043431739147446225921/103318551739147446225921 : ℝ)))) := by
      rw [Real.arctan_neg, ztg_atan_shift_add (by norm_num : (-1:ℝ) < ((44637560000000000000000/58680991739147446225921 : ℝ)))]
      norm_num
    have htp := g4v_atan_pos_bounds (x := ((14043431739147446225921/103318551739147446225921 : ℝ))) (lo := ((8443481537709/62500000000000 : ℝ))) (hi := ((8443481787709/62500000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hp := Kepler.Text.g4v_pi_bounds
    have hfin : Real.arctan (-((44637560000000000000000/58680991739147446225921 : ℝ))) ≤ ((-130060490958820861923/200000000000000000000 : ℝ)) := by
      rw [hshift]
      linarith [htn.1, htn.2, hp.1, hp.2]
    exact hfin

theorem ztgcHM_t48_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t48 : ((121618696107134461923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((243241018979273723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t48_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((131127670769861329099011/2000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) (dlo := ((131127670769861329099011/2000000000000000000000 : ℝ))) (dhi := ((655664209986645209330981/10000000000000000000000 : ℝ)))
    (ulo := (-((48551446323200000000000/131127670769861329099011 : ℝ)))) (uhi := (-((18673330000000000000000/50435708460511169948537 : ℝ))))
    (lo := ((-11081542647611/31250000000000 : ℝ))) (hi := ((-11080976028079/31250000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((131127670769861329099011/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((48551446323200000000000/131127670769861329099011 : ℝ))) * ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((655664209986645209330981/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/50435708460511169948537 : ℝ))) * ((655664209986645209330981/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((48551446323200000000000/131127670769861329099011 : ℝ))) (lo := ((11081542522611/31250000000000 : ℝ))) (hi := ((11081542647611/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-11081542647611/31250000000000 : ℝ)) ≤ Real.arctan (-((48551446323200000000000/131127670769861329099011 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/50435708460511169948537 : ℝ))) (lo := ((11080976028079/31250000000000 : ℝ))) (hi := ((11080976153079/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/50435708460511169948537 : ℝ))) ≤ ((-11080976028079/31250000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t49_delta : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
  have hE : deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by
    norm_num
  have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
    have hf := ztgcHM_f0
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t49 : ((121618696107134461923/100000000000000000000 : ℝ)) ≤ dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((243241018979273723847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t49_delta
  have hE4 : deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcHM_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((131127670769861329099011/2000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((655664209986645209330981/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) (dlo := ((131127670769861329099011/2000000000000000000000 : ℝ))) (dhi := ((655664209986645209330981/10000000000000000000000 : ℝ)))
    (ulo := (-((48551446323200000000000/131127670769861329099011 : ℝ)))) (uhi := (-((18673330000000000000000/50435708460511169948537 : ℝ))))
    (lo := ((-11081542647611/31250000000000 : ℝ))) (hi := ((-11080976028079/31250000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((131127670769861329099011/2000000000000000000000 : ℝ))), hE4]
    have hnum : (-((48551446323200000000000/131127670769861329099011 : ℝ))) * ((131127670769861329099011/2000000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((655664209986645209330981/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/50435708460511169948537 : ℝ))) * ((655664209986645209330981/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((48551446323200000000000/131127670769861329099011 : ℝ))) (lo := ((11081542522611/31250000000000 : ℝ))) (hi := ((11081542647611/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-11081542647611/31250000000000 : ℝ)) ≤ Real.arctan (-((48551446323200000000000/131127670769861329099011 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/50435708460511169948537 : ℝ))) (lo := ((11080976028079/31250000000000 : ℝ))) (hi := ((11080976153079/31250000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/50435708460511169948537 : ℝ))) ≤ ((-11080976028079/31250000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t50_delta : ((1379469530174723/4000000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((131561339804680643/381469726562500 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t50 : ((131145528701101761923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((262293184294343323847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t50_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 = ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((157664/125 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) ≤ ((3941632/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((15172326976/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/62500000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((58402079612368/30517578125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((224804204947907524/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((114371715498421284387207/1250000000000000000000 : ℝ)) ^ 2 ≤ ((33487076690466828308867/4000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((31188932264332167044592587/3725290298461914062500 : ℝ)) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2)))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) (dlo := ((114371715498421284387207/1250000000000000000000 : ℝ))) (dhi := ((914998102253417101338419/10000000000000000000000 : ℝ)))
    (ulo := (-((30344653952000000000000/114371715498421284387207 : ℝ)))) (uhi := (-((18673330000000000000000/70384469404109007795263 : ℝ))))
    (lo := ((-259341038783879/1000000000000000 : ℝ))) (hi := ((-12966520316159/50000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((114371715498421284387207/1250000000000000000000 : ℝ))), hE4]
    have hnum : (-((30344653952000000000000/114371715498421284387207 : ℝ))) * ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((914998102253417101338419/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/70384469404109007795263 : ℝ))) * ((914998102253417101338419/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((30344653952000000000000/114371715498421284387207 : ℝ))) (lo := ((259341034783879/1000000000000000 : ℝ))) (hi := ((259341038783879/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-259341038783879/1000000000000000 : ℝ)) ≤ Real.arctan (-((30344653952000000000000/114371715498421284387207 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/70384469404109007795263 : ℝ))) (lo := ((12966520316159/50000000000000 : ℝ))) (hi := ((12966520516159/50000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/70384469404109007795263 : ℝ))) ≤ ((-12966520316159/50000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t51_delta : ((1379469530174723/4000000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t51 : ((131145528701101761923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((262293184294343323847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t51_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) = ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((157664/125 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) ≤ ((3941632/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((15172326976/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/62500000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((58402079612368/30517578125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((224804204947907524/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((114371715498421284387207/1250000000000000000000 : ℝ)) ^ 2 ≤ ((33487076690466828308867/4000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((31188932264332167044592587/3725290298461914062500 : ℝ)) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) (dlo := ((114371715498421284387207/1250000000000000000000 : ℝ))) (dhi := ((914998102253417101338419/10000000000000000000000 : ℝ)))
    (ulo := (-((30344653952000000000000/114371715498421284387207 : ℝ)))) (uhi := (-((18673330000000000000000/70384469404109007795263 : ℝ))))
    (lo := ((-259341038783879/1000000000000000 : ℝ))) (hi := ((-12966520316159/50000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((114371715498421284387207/1250000000000000000000 : ℝ))), hE4]
    have hnum : (-((30344653952000000000000/114371715498421284387207 : ℝ))) * ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((914998102253417101338419/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/70384469404109007795263 : ℝ))) * ((914998102253417101338419/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((30344653952000000000000/114371715498421284387207 : ℝ))) (lo := ((259341034783879/1000000000000000 : ℝ))) (hi := ((259341038783879/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-259341038783879/1000000000000000 : ℝ)) ≤ Real.arctan (-((30344653952000000000000/114371715498421284387207 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/70384469404109007795263 : ℝ))) (lo := ((12966520316159/50000000000000 : ℝ))) (hi := ((12966520516159/50000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/70384469404109007795263 : ℝ))) ≤ ((-12966520316159/50000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t52_delta : ((1379469530174723/4000000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t52 : ((97566948881277561923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((195140569317440123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t52_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((991064266174723/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((94519525898430643/1525878906250000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((991064266174723/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((94519525898430643/1525878906250000 : ℝ)) := by
      have hf := ztgcHM_f13
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) = ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((157664/125 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) ≤ ((3941632/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((15172326976/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/62500000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((58402079612368/30517578125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((224804204947907524/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((114371715498421284387207/1250000000000000000000 : ℝ)) ^ 2 ≤ ((33487076690466828308867/4000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((31188932264332167044592587/3725290298461914062500 : ℝ)) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((94519525898430643/1525878906250000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) (dlo := ((114371715498421284387207/1250000000000000000000 : ℝ))) (dhi := ((914998102253417101338419/10000000000000000000000 : ℝ)))
    (ulo := (-((77430395615994382745600/114371715498421284387207 : ℝ)))) (uhi := (-((47647320489169375000000/70384469404109007795263 : ℝ))))
    (lo := ((-595126836982121/1000000000000000 : ℝ))) (hi := ((-37193342575481/62500000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((114371715498421284387207/1250000000000000000000 : ℝ))), hE4]
    have hnum : (-((77430395615994382745600/114371715498421284387207 : ℝ))) * ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ ((-94519525898430643/1525878906250000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((914998102253417101338419/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-991064266174723/16000000000000 : ℝ)) ≤ (-((47647320489169375000000/70384469404109007795263 : ℝ))) * ((914998102253417101338419/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((77430395615994382745600/114371715498421284387207 : ℝ))) (lo := ((595126832982121/1000000000000000 : ℝ))) (hi := ((595126836982121/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-595126836982121/1000000000000000 : ℝ)) ≤ Real.arctan (-((77430395615994382745600/114371715498421284387207 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((47647320489169375000000/70384469404109007795263 : ℝ))) (lo := ((37193342575481/62500000000000 : ℝ))) (hi := ((37193342825481/62500000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((47647320489169375000000/70384469404109007795263 : ℝ))) ≤ ((-37193342575481/62500000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t53_delta : ((1379469530174723/4000000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t53 : ((131145528701101761923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((262293184294343323847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t53_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) = ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((157664/125 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) ≤ ((3941632/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((15172326976/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/62500000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((58402079612368/30517578125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((224804204947907524/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((114371715498421284387207/1250000000000000000000 : ℝ)) ^ 2 ≤ ((33487076690466828308867/4000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((31188932264332167044592587/3725290298461914062500 : ℝ)) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) (dlo := ((114371715498421284387207/1250000000000000000000 : ℝ))) (dhi := ((914998102253417101338419/10000000000000000000000 : ℝ)))
    (ulo := (-((30344653952000000000000/114371715498421284387207 : ℝ)))) (uhi := (-((18673330000000000000000/70384469404109007795263 : ℝ))))
    (lo := ((-259341038783879/1000000000000000 : ℝ))) (hi := ((-12966520316159/50000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((114371715498421284387207/1250000000000000000000 : ℝ))), hE4]
    have hnum : (-((30344653952000000000000/114371715498421284387207 : ℝ))) * ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((914998102253417101338419/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/70384469404109007795263 : ℝ))) * ((914998102253417101338419/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((30344653952000000000000/114371715498421284387207 : ℝ))) (lo := ((259341034783879/1000000000000000 : ℝ))) (hi := ((259341038783879/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-259341038783879/1000000000000000 : ℝ)) ≤ Real.arctan (-((30344653952000000000000/114371715498421284387207 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/70384469404109007795263 : ℝ))) (lo := ((12966520316159/50000000000000 : ℝ))) (hi := ((12966520516159/50000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/70384469404109007795263 : ℝ))) ≤ ((-12966520316159/50000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t54_delta : ((1379469530174723/4000000000000 : ℝ)) ≤ deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
  have hE : deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t54 : ((131145528701101761923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((262293184294343323847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t54_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact hp2
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) = ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((157664/125 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) ≤ ((3941632/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((15172326976/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/62500000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((58402079612368/30517578125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((224804204947907524/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((33487076690466828308867/4000000000000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((31188932264332167044592587/3725290298461914062500 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact hp5
  have hsA : ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((114371715498421284387207/1250000000000000000000 : ℝ)) ^ 2 ≤ ((33487076690466828308867/4000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((31188932264332167044592587/3725290298461914062500 : ℝ)) ≤ ((914998102253417101338419/10000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) (dlo := ((114371715498421284387207/1250000000000000000000 : ℝ))) (dhi := ((914998102253417101338419/10000000000000000000000 : ℝ)))
    (ulo := (-((30344653952000000000000/114371715498421284387207 : ℝ)))) (uhi := (-((18673330000000000000000/70384469404109007795263 : ℝ))))
    (lo := ((-259341038783879/1000000000000000 : ℝ))) (hi := ((-12966520316159/50000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((114371715498421284387207/1250000000000000000000 : ℝ))), hE4]
    have hnum : (-((30344653952000000000000/114371715498421284387207 : ℝ))) * ((114371715498421284387207/1250000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((914998102253417101338419/10000000000000000000000 : ℝ))), hE4]
    have hnum : ((-24275329/1000000 : ℝ)) ≤ (-((18673330000000000000000/70384469404109007795263 : ℝ))) * ((914998102253417101338419/10000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((30344653952000000000000/114371715498421284387207 : ℝ))) (lo := ((259341034783879/1000000000000000 : ℝ))) (hi := ((259341038783879/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-259341038783879/1000000000000000 : ℝ)) ≤ Real.arctan (-((30344653952000000000000/114371715498421284387207 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((18673330000000000000000/70384469404109007795263 : ℝ))) (lo := ((12966520316159/50000000000000 : ℝ))) (hi := ((12966520516159/50000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((18673330000000000000000/70384469404109007795263 : ℝ))) ≤ ((-12966520316159/50000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t55_delta : ((1379469530174723/4000000000000 : ℝ)) ≤ deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
  have hE : deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by
    norm_num
  have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
    have hf := ztgcHM_f6
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  exact hp3

theorem ztgcHM_t55 : ((115778844869647661923/100000000000000000000 : ℝ)) ≤ dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((231560833507112523847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t55_delta
  have hE4 : deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have h4 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((16275329/500000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((317885218/9765625 : ℝ)) := by
      have hf := ztgcHM_f5
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact hp1
  have hE2 : 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) = ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaY deltaX; ring
  have hA2 : ((1379469530174723/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((526245359218722572/95367431640625 : ℝ)) := by
    have hp0 : ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) ∧ ((1024/1 : ℝ)) ≤ ((1024/1 : ℝ)) := by
      norm_num
    have hp1 : ((157664/125 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) ≤ ((3941632/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/15625 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((15172326976/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1379469530174723/250000000000 : ℝ)) ≤ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((1024/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((526245359218722572/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f6
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact hp3
  have hsA : ((742824212695246786561929/10000000000000000000000 : ℝ)) ≤ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((371418986756111986384693/5000000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((742824212695246786561929/10000000000000000000000 : ℝ)) ^ 2 ≤ ((1379469530174723/250000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((526245359218722572/95367431640625 : ℝ)) ≤ ((371418986756111986384693/5000000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((317885218/9765625 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * (2 * 2) * deltaY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) (dlo := ((742824212695246786561929/10000000000000000000000 : ℝ))) (dhi := ((371418986756111986384693/5000000000000000000000 : ℝ)))
    (ulo := (-((325514463232000000000000/742824212695246786561929 : ℝ)))) (uhi := (-((23250470000000000000000/53059855250873140912099 : ℝ))))
    (lo := ((-20650393854921/50000000000000 : ℝ))) (hi := ((-206496080129667/500000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((742824212695246786561929/10000000000000000000000 : ℝ))), hE4]
    have hnum : (-((325514463232000000000000/742824212695246786561929 : ℝ))) * ((742824212695246786561929/10000000000000000000000 : ℝ)) ≤ ((-317885218/9765625 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((371418986756111986384693/5000000000000000000000 : ℝ))), hE4]
    have hnum : ((-16275329/500000 : ℝ)) ≤ (-((23250470000000000000000/53059855250873140912099 : ℝ))) * ((371418986756111986384693/5000000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((325514463232000000000000/742824212695246786561929 : ℝ))) (lo := ((20650393654921/50000000000000 : ℝ))) (hi := ((20650393854921/50000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-20650393854921/50000000000000 : ℝ)) ≤ Real.arctan (-((325514463232000000000000/742824212695246786561929 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((23250470000000000000000/53059855250873140912099 : ℝ))) (lo := ((206496080129667/500000000000000 : ℝ))) (hi := ((206496082129667/500000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((23250470000000000000000/53059855250873140912099 : ℝ))) ≤ ((-206496080129667/500000000000000 : ℝ)) := by linarith
    exact hfin

theorem ztgcHM_t56_delta : ((14305247419799561436289/32000000000000000000 : ℝ)) ≤ deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((13323448840036601566947529/29802322387695312500000 : ℝ)) := by
  have hE : deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) = ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) := by
    unfold deltaY deltaX; ring
  rw [hE]
  have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by
    norm_num
  have hp1 : ((19708/125 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) ≤ ((492704/3125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
  have hp2 : ((24275329/125000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) ≤ ((1896540872/9765625 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
  have hp3 : ((119604545983/500000000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((7300259951546/30517578125 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
  have hp4 : ((589291598058241/2000000000000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/190734863281250 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
  have hp5 : ((2903439703632953407/8000000000000000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((865327585895733036757/2384185791015625000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
  have hp6 : ((14305247419799561436289/32000000000000000000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((13323448840036601566947529/29802322387695312500000 : ℝ)) := by
    have hf := ztgcHM_f1
    constructor <;> nlinarith [hp5.1, hp5.2, hf.1, hf.2]
  exact hp6

theorem ztgcHM_t56 : ((123094920830703561923/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((246193925223346123847/200000000000000000000 : ℝ)) := by
  have hD := ztgcHM_t56_delta
  have hE4 : deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have h4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by
      norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/4000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((3650129975773/122070312500 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    exact hp4
  have hE2 : 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) = ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) := by
    unfold deltaY deltaX; ring
  have hA2 : ((347264587542035467921628014081/32000000000000000000000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((3158558160141300605961904128488161/291038304567337036132812500000 : ℝ)) := by
    have hp0 : ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) ∧ ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) := by
      norm_num
    have hp1 : ((315328/125 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) ≤ ((7883264/3125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((48550658/15625 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) ≤ ((30344653952/9765625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/31250000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((116804159224736/30517578125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/125000000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((449608409895815048/95367431640625 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((2903439703632953407/500000000000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((1730655171791466073514/298023223876953125 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    have hp6 : ((14305247419799561436289/2000000000000000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((13323448840036601566947529/1862645149230957031250 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp5.1, hp5.2, hf.1, hf.2]
    have hp7 : ((70481954037352439196595903/8000000000000000000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((205141141790043554326291104013/23283064365386962890625000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp6.1, hp6.2, hf.1, hf.2]
    have hp8 : ((347264587542035467921628014081/32000000000000000000000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((3158558160141300605961904128488161/291038304567337036132812500000 : ℝ)) := by
      have hf := ztgcHM_f1
      constructor <;> nlinarith [hp7.1, hp7.2, hf.1, hf.2]
    exact hp8
  have hsA : ((10417302116663697872919/100000000000000000000 : ℝ)) ≤ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((26044101085901101059857/250000000000000000000 : ℝ)) := by
    refine ztg_sqrt_bounds (by norm_num) (by norm_num) ?_ ?_
    · rw [hE2]; exact le_trans (by norm_num : ((10417302116663697872919/100000000000000000000 : ℝ)) ^ 2 ≤ ((347264587542035467921628014081/32000000000000000000000000 : ℝ))) hA2.1
    · rw [hE2]; exact le_trans hA2.2 (by norm_num : ((3158558160141300605961904128488161/291038304567337036132812500000 : ℝ)) ≤ ((26044101085901101059857/250000000000000000000 : ℝ)) ^ 2)
  have habs : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    rw [abs_neg, abs_le, hE4]
    constructor <;> linarith [h4.1, h4.2]
  have hbr : |-(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)))| < Real.sqrt (4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) := by
    exact lt_of_le_of_lt habs (by linarith [hsA.1])
  rw [ztg_dihY_eq_br1 hbr]
  have hw := g4v_atan_ratio_neg_bounds (t := -(deltaX4 ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus))))
    (d := 4 * ((2 * hminus) * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) (dlo := ((10417302116663697872919/100000000000000000000 : ℝ))) (dhi := ((26044101085901101059857/250000000000000000000 : ℝ)))
    (ulo := (-((3683192093866516873216/10417302116663697872919 : ℝ)))) (uhi := (-((708283170743078125000/2003392391223161619989 : ℝ))))
    (lo := ((-339847117487861/1000000000000000 : ℝ))) (hi := ((-169913350839083/500000000000000 : ℝ)))
    (by norm_num) hsA.1 hsA.2 ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith
  · rw [hE4]; linarith [h4.1, h4.2]
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < ((10417302116663697872919/100000000000000000000 : ℝ))), hE4]
    have hnum : (-((3683192093866516873216/10417302116663697872919 : ℝ))) * ((10417302116663697872919/100000000000000000000 : ℝ)) ≤ ((-56201051236976881/1525878906250000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((26044101085901101059857/250000000000000000000 : ℝ))), hE4]
    have hnum : ((-589291598058241/16000000000000 : ℝ)) ≤ (-((708283170743078125000/2003392391223161619989 : ℝ))) * ((26044101085901101059857/250000000000000000000 : ℝ)) := by norm_num
    linarith [hnum, h4.1, h4.2]
  · have htp := g4v_atan_pos_bounds (x := ((3683192093866516873216/10417302116663697872919 : ℝ))) (lo := ((339847113487861/1000000000000000 : ℝ))) (hi := ((339847117487861/1000000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : ((-339847117487861/1000000000000000 : ℝ)) ≤ Real.arctan (-((3683192093866516873216/10417302116663697872919 : ℝ))) := by linarith
    exact hfin
  · have htp := g4v_atan_pos_bounds (x := ((708283170743078125000/2003392391223161619989 : ℝ))) (lo := ((169913350839083/500000000000000 : ℝ))) (hi := ((169913352839083/500000000000000 : ℝ)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have htn := g4v_atan_neg_bounds htp
    have hfin : Real.arctan (-((708283170743078125000/2003392391223161619989 : ℝ))) ≤ ((-169913350839083/500000000000000 : ℝ)) := by linarith
    exact hfin


/-! ## 3. The 31 corner certificates -/

theorem ztgcHM_c0 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 2 2 2 (2 * hminus) := by
  have hS : ((221403382501/100000000000 : ℝ)) ≤ solY (2 * hminus) 2 2 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 2 + solY 2 2 2 (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 2 ∧ solY (2 * hminus) 2 2 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 2 + solY 2 2 2 (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 2 ≤ ((221431186241/100000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t0
    have hs1 := ztgcHM_t1
    have hs2 := ztgcHM_t3
    have hs3 := ztgcHM_t4
    have hs4 := ztgcHM_t5
    have hs5 := ztgcHM_t6
    have hs6 := ztgcHM_t8
    have hs7 := ztgcHM_t9
    have hs8 := ztgcHM_t10
    have hs9 := ztgcHM_t12
    have hs10 := ztgcHM_t13
    have hs11 := ztgcHM_t14
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((522202009109/100000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ≤ ((104444452907/20000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((121618696107134461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 2 2 2 (2 * hminus) ≤ (0.108654) * ((243241018979273723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t4
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((121618696107134461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ≤ (0.108654) * ((243241018979273723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t0
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t10
    have hdt2 := ztgcHM_t6
    have hdt3 := ztgcHM_t12
    have hdt4 := ztgcHM_t5
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hdt2.1, hdt2.2, hdt3.1, hdt3.2, hdt4.1, hdt4.2, hprod5.1, hprod5.2]
  have hV : ((3465374481/3125000000 : ℝ)) ≤ volY (2 * hminus) 2 2 2 2 (2 * hminus) ∧ volY (2 * hminus) 2 2 2 2 (2 * hminus) ≤ ((3465489259/3125000000 : ℝ)) := by
    have hDm := ztgcHM_t4_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) 2 2 2 2 (2 * hminus) from rfl]
    have hsD : ((133070500070896499796033/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 2 2 2 (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) 2 2 2 2 (2 * hminus)) ≤ ((4158583360817583356659/312500000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((133070500070896499796033/10000000000000000000000 : ℝ)) ^ 2 ≤ ((16887434029134686/95367431640625 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((708354684284159/4000000000000 : ℝ)) ≤ ((4158583360817583356659/312500000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := 2) (y4 := 2) (y5 := 2) (y6 := (2 * hminus))
    (Vlo := ((3465374481/3125000000 : ℝ))) (Vhi := ((3465489259/3125000000 : ℝ)))
    (Slo := ((221403382501/100000000000 : ℝ))) (Shi := ((221431186241/100000000000 : ℝ)))
    (Dlo := ((522202009109/100000000000 : ℝ))) (Dhi := ((104444452907/20000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((80684113857107643/4000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 2 2 2 (2 * hminus) lmfun := by
    have heval : ((80684113857107643/4000000000000000000 : ℝ)) ≤ (((3465374481/3125000000 : ℝ)) - (0.6443107122) * ((221431186241/100000000000 : ℝ)) + (0.0647174928) * ((522202009109/100000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 2 2 2 (2 * hminus) ((80684113857107643/4000000000000000000 : ℝ)) ((121618696107134461923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t4
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c1 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 2 2 (2 * hminus) 2 := by
  have hS : ((221403382501/100000000000 : ℝ)) ≤ solY (2 * hminus) 2 2 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 2 + solY 2 (2 * hminus) 2 (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) 2 ∧ solY (2 * hminus) 2 2 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 2 + solY 2 (2 * hminus) 2 (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) 2 ≤ ((221431186241/100000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t0
    have hs1 := ztgcHM_t1
    have hs2 := ztgcHM_t3
    have hs3 := ztgcHM_t4
    have hs4 := ztgcHM_t5
    have hs5 := ztgcHM_t6
    have hs6 := ztgcHM_t8
    have hs7 := ztgcHM_t9
    have hs8 := ztgcHM_t10
    have hs9 := ztgcHM_t12
    have hs10 := ztgcHM_t13
    have hs11 := ztgcHM_t14
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((522202009109/100000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 ≤ ((104444452907/20000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((121618696107134461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) 2 2 2 (2 * hminus) 2 ≤ (0.108654) * ((243241018979273723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t3
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((121618696107134461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ≤ (0.108654) * ((243241018979273723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t0
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t9
    have hdt2 := ztgcHM_t8
    have hdt3 := ztgcHM_t9
    have hdt5 := ztgcHM_t5
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hdt2.1, hdt2.2, hdt3.1, hdt3.2, hprod4.1, hprod4.2, hdt5.1, hdt5.2]
  have hV : ((3465374481/3125000000 : ℝ)) ≤ volY (2 * hminus) 2 2 2 (2 * hminus) 2 ∧ volY (2 * hminus) 2 2 2 (2 * hminus) 2 ≤ ((3465489259/3125000000 : ℝ)) := by
    have hDm := ztgcHM_t3_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = deltaY (2 * hminus) 2 2 2 (2 * hminus) 2 from rfl]
    have hsD : ((133070500070896499796033/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 2 2 (2 * hminus) 2) ∧ Real.sqrt (deltaY (2 * hminus) 2 2 2 (2 * hminus) 2) ≤ ((4158583360817583356659/312500000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((133070500070896499796033/10000000000000000000000 : ℝ)) ^ 2 ≤ ((16887434029134686/95367431640625 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((708354684284159/4000000000000 : ℝ)) ≤ ((4158583360817583356659/312500000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := 2) (y4 := 2) (y5 := (2 * hminus)) (y6 := 2)
    (Vlo := ((3465374481/3125000000 : ℝ))) (Vhi := ((3465489259/3125000000 : ℝ)))
    (Slo := ((221403382501/100000000000 : ℝ))) (Shi := ((221431186241/100000000000 : ℝ)))
    (Dlo := ((522202009109/100000000000 : ℝ))) (Dhi := ((104444452907/20000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((80684113857107643/4000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 2 2 (2 * hminus) 2 lmfun := by
    have heval : ((80684113857107643/4000000000000000000 : ℝ)) ≤ (((3465374481/3125000000 : ℝ)) - (0.6443107122) * ((221431186241/100000000000 : ℝ)) + (0.0647174928) * ((522202009109/100000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 2 2 (2 * hminus) 2 ((80684113857107643/4000000000000000000 : ℝ)) ((121618696107134461923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t3
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c2 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) := by
  have hS : ((899645979/400000000 : ℝ)) ≤ solY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + solY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ solY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + solY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((224922677263/100000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t15
    have hs1 := ztgcHM_t24
    have hs2 := ztgcHM_t29
    have hs3 := ztgcHM_t31
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hp1, hp2]
  have hD : ((431163651191/100000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ≤ ((215589342647/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((115778844869647661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((231560833507112523847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t24
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((115778844869647661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ≤ (0.108654) * ((231560833507112523847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t15
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((115778844869647661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ≤ (0.108654) * ((231560833507112523847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t15
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t31
    have hdt2 := ztgcHM_t29
    have hdt3 := ztgcHM_t31
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hdt2.1, hdt2.2, hdt3.1, hdt3.2, hprod4.1, hprod4.2, hprod5.1, hprod5.2]
  have hV : ((125638255439/100000000000 : ℝ)) ≤ volY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) ≤ ((125639762879/100000000000 : ℝ)) := by
    have hDm := ztgcHM_t24_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) from rfl]
    have hsD : ((1507660265263339733229/100000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus)) ≤ ((150767595455328595304561/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((1507660265263339733229/100000000000000000000 : ℝ)) ^ 2 ≤ ((56825987/250000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((2219811308/9765625 : ℝ)) ≤ ((150767595455328595304561/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := 2) (y4 := 2) (y5 := (2 * hminus)) (y6 := (2 * hminus))
    (Vlo := ((125638255439/100000000000 : ℝ))) (Vhi := ((125639762879/100000000000 : ℝ)))
    (Slo := ((899645979/400000000 : ℝ))) (Shi := ((224922677263/100000000000 : ℝ)))
    (Dlo := ((431163651191/100000000000 : ℝ))) (Dhi := ((215589342647/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((43109977766604886081/500000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) lmfun := by
    have heval : ((43109977766604886081/500000000000000000000 : ℝ)) ≤ (((125638255439/100000000000 : ℝ)) - (0.6443107122) * ((224922677263/100000000000 : ℝ)) + (0.0647174928) * ((431163651191/100000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) ((43109977766604886081/500000000000000000000 : ℝ)) ((115778844869647661923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t24
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c3 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 2 (2 * hminus) 2 2 := by
  have hS : ((47991094857/25000000000 : ℝ)) ≤ solY (2 * hminus) 2 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 2 ∧ solY (2 * hminus) 2 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 2 ≤ ((38402129677/20000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t2
    have hs1 := ztgcHM_t7
    have hs2 := ztgcHM_t11
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hp1, hp2]
  have hD : ((10108050421/2500000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) 2 ≤ ((404351522959/100000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((179483979196087561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) 2 2 ≤ (0.108654) * ((358976628550370923847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t2
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((179483979196087561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) 2 2 ≤ (0.108654) * ((358976628550370923847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t2
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t11
    have hdt2 := ztgcHM_t7
    have hdt4 := ztgcHM_t7
    have hdt5 := ztgcHM_t7
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hdt2.1, hdt2.2, hprod3.1, hprod3.2, hdt4.1, hdt4.2, hdt5.1, hdt5.2]
  have hV : ((198777563453/200000000000 : ℝ)) ≤ volY (2 * hminus) 2 2 (2 * hminus) 2 2 ∧ volY (2 * hminus) 2 2 (2 * hminus) 2 2 ≤ ((993931315783/1000000000000 : ℝ)) := by
    have hDm := ztgcHM_t2_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = deltaY (2 * hminus) 2 2 (2 * hminus) 2 2 from rfl]
    have hsD : ((119266658071856341808877/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 2 (2 * hminus) 2 2) ∧ Real.sqrt (deltaY (2 * hminus) 2 2 (2 * hminus) 2 2) ≤ ((119271637893974637774703/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((119266658071856341808877/10000000000000000000000 : ℝ)) ^ 2 ≤ ((44451674237744075884231/312500000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((434134630659789440331151/3051757812500000000000 : ℝ)) ≤ ((119271637893974637774703/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := 2) (y4 := (2 * hminus)) (y5 := 2) (y6 := 2)
    (Vlo := ((198777563453/200000000000 : ℝ))) (Vhi := ((993931315783/1000000000000 : ℝ)))
    (Slo := ((47991094857/25000000000 : ℝ))) (Shi := ((38402129677/20000000000 : ℝ)))
    (Dlo := ((10108050421/2500000000 : ℝ))) (Dhi := ((404351522959/100000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((368194265860209791/20000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 2 (2 * hminus) 2 2 lmfun := by
    have heval : ((368194265860209791/20000000000000000000 : ℝ)) ≤ (((198777563453/200000000000 : ℝ)) - (0.6443107122) * ((38402129677/20000000000 : ℝ)) + (0.0647174928) * ((10108050421/2500000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 2 (2 * hminus) 2 2 ((368194265860209791/20000000000000000000 : ℝ)) ((179483979196087561923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t2
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c4 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) := by
  have hS : ((10434647031/5000000000 : ℝ)) ≤ solY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ∧ solY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ≤ ((52183185673/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t17
    have hs1 := ztgcHM_t19
    have hs2 := ztgcHM_t23
    have hs3 := ztgcHM_t27
    have hs4 := ztgcHM_t28
    have hs5 := ztgcHM_t33
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((178933794511/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ≤ ((357895952499/100000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t23
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t22
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((103917101337874261923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ≤ (0.108654) * ((207845085209607923847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t17
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t33
    have hdt2 := ztgcHM_t28
    have hdt4 := ztgcHM_t26
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hdt2.1, hdt2.2, hprod3.1, hprod3.2, hdt4.1, hdt4.2, hprod5.1, hprod5.2]
  have hV : ((59119943111/50000000000 : ℝ)) ≤ volY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ∧ volY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((11824470157/10000000000 : ℝ)) := by
    have hDm := ztgcHM_t23_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) from rfl]
    have hsD : ((141887983465829016392283/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus)) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((141887983465829016392283/10000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/1250000000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((1228867890169579548417611/6103515625000000000000 : ℝ)) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := 2) (y4 := (2 * hminus)) (y5 := 2) (y6 := (2 * hminus))
    (Vlo := ((59119943111/50000000000 : ℝ))) (Vhi := ((11824470157/10000000000 : ℝ)))
    (Slo := ((10434647031/5000000000 : ℝ))) (Shi := ((52183185673/25000000000 : ℝ)))
    (Dlo := ((178933794511/50000000000 : ℝ))) (Dhi := ((357895952499/100000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) lmfun := by
    have heval : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ (((59119943111/50000000000 : ℝ)) - (0.6443107122) * ((52183185673/25000000000 : ℝ)) + (0.0647174928) * ((178933794511/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ((8639296543178473499/125000000000000000000 : ℝ)) ((158274604480857171923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t23
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c5 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 := by
  have hS : ((10434647031/5000000000 : ℝ)) ≤ solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ∧ solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ≤ ((52183185673/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t16
    have hs1 := ztgcHM_t21
    have hs2 := ztgcHM_t22
    have hs3 := ztgcHM_t26
    have hs4 := ztgcHM_t30
    have hs5 := ztgcHM_t32
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((178933794511/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ ((357895952499/100000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t22
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t19
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((103917101337874261923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ≤ (0.108654) * ((207845085209607923847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t17
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t32
    have hdt2 := ztgcHM_t30
    have hdt5 := ztgcHM_t26
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hdt2.1, hdt2.2, hprod3.1, hprod3.2, hprod4.1, hprod4.2, hdt5.1, hdt5.2]
  have hV : ((59119943111/50000000000 : ℝ)) ≤ volY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ∧ volY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ≤ ((11824470157/10000000000 : ℝ)) := by
    have hDm := ztgcHM_t22_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 from rfl]
    have hsD : ((141887983465829016392283/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((141887983465829016392283/10000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/1250000000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((1228867890169579548417611/6103515625000000000000 : ℝ)) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := 2) (y4 := (2 * hminus)) (y5 := (2 * hminus)) (y6 := 2)
    (Vlo := ((59119943111/50000000000 : ℝ))) (Vhi := ((11824470157/10000000000 : ℝ)))
    (Slo := ((10434647031/5000000000 : ℝ))) (Shi := ((52183185673/25000000000 : ℝ)))
    (Dlo := ((178933794511/50000000000 : ℝ))) (Dhi := ((357895952499/100000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 lmfun := by
    have heval : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ (((59119943111/50000000000 : ℝ)) - (0.6443107122) * ((52183185673/25000000000 : ℝ)) + (0.0647174928) * ((178933794511/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 ((8639296543178473499/125000000000000000000 : ℝ)) ((158274604480857171923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t22
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c6 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) := by
  have hS : ((4394492911/2000000000 : ℝ)) ≤ solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((54940412683/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t35
    have hs1 := ztgcHM_t36
    have hs2 := ztgcHM_t37
    have hs3 := ztgcHM_t39
    have hs4 := ztgcHM_t40
    have hs5 := ztgcHM_t41
    have hs6 := ztgcHM_t43
    have hs7 := ztgcHM_t44
    have hs8 := ztgcHM_t45
    have hs9 := ztgcHM_t46
    have hs10 := ztgcHM_t48
    have hs11 := ztgcHM_t49
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((74248895423/25000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ ((148510158353/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((147891111982938951923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((295792839738049903847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t44
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((142667648658134061923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((285338562236501123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t41
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t36
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t36
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t49
    have hdt2 := ztgcHM_t48
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hdt2.1, hdt2.2, hprod3.1, hprod3.2, hprod4.1, hprod4.2, hprod5.1, hprod5.2]
  have hV : ((136591223719/100000000000 : ℝ)) ≤ volY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((68298405207/50000000000 : ℝ)) := by
    have hDm := ztgcHM_t44_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) from rfl]
    have hsD : ((40977397115581602843441/2500000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((40977397115581602843441/2500000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((167927951327195450705831/625000000000000000000 : ℝ)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := 2) (y4 := (2 * hminus)) (y5 := (2 * hminus)) (y6 := (2 * hminus))
    (Vlo := ((136591223719/100000000000 : ℝ))) (Vhi := ((68298405207/50000000000 : ℝ)))
    (Slo := ((4394492911/2000000000 : ℝ))) (Shi := ((54940412683/25000000000 : ℝ)))
    (Dlo := ((74248895423/25000000000 : ℝ))) (Dhi := ((148510158353/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) lmfun := by
    have heval : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ (((136591223719/100000000000 : ℝ)) - (0.6443107122) * ((54940412683/25000000000 : ℝ)) + (0.0647174928) * ((74248895423/25000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ((17771559301751563109/125000000000000000000 : ℝ)) ((147891111982938951923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t44
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c7 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 (2 * hminus) 2 2 2 := by
  have hS : ((221403382501/100000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 2 2 + solY (2 * hminus) 2 2 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 2 2 + solY (2 * hminus) 2 2 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((221431186241/100000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t0
    have hs1 := ztgcHM_t1
    have hs2 := ztgcHM_t3
    have hs3 := ztgcHM_t4
    have hs4 := ztgcHM_t5
    have hs5 := ztgcHM_t6
    have hs6 := ztgcHM_t8
    have hs7 := ztgcHM_t9
    have hs8 := ztgcHM_t10
    have hs9 := ztgcHM_t12
    have hs10 := ztgcHM_t13
    have hs11 := ztgcHM_t14
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((522202009109/100000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((104444452907/20000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((121618696107134461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 ≤ (0.108654) * ((243241018979273723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t1
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((121618696107134461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ≤ (0.108654) * ((243241018979273723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t0
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t5
    have hdt3 := ztgcHM_t6
    have hdt4 := ztgcHM_t8
    have hdt5 := ztgcHM_t6
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hprod2.1, hprod2.2, hdt3.1, hdt3.2, hdt4.1, hdt4.2, hdt5.1, hdt5.2]
  have hV : ((3465374481/3125000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) 2 2 2 ∧ volY (2 * hminus) 2 (2 * hminus) 2 2 2 ≤ ((3465489259/3125000000 : ℝ)) := by
    have hDm := ztgcHM_t1_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = deltaY (2 * hminus) 2 (2 * hminus) 2 2 2 from rfl]
    have hsD : ((133070500070896499796033/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) 2 2 2) ∧ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) 2 2 2) ≤ ((4158583360817583356659/312500000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((133070500070896499796033/10000000000000000000000 : ℝ)) ^ 2 ≤ ((16887434029134686/95367431640625 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((708354684284159/4000000000000 : ℝ)) ≤ ((4158583360817583356659/312500000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := (2 * hminus)) (y4 := 2) (y5 := 2) (y6 := 2)
    (Vlo := ((3465374481/3125000000 : ℝ))) (Vhi := ((3465489259/3125000000 : ℝ)))
    (Slo := ((221403382501/100000000000 : ℝ))) (Shi := ((221431186241/100000000000 : ℝ)))
    (Dlo := ((522202009109/100000000000 : ℝ))) (Dhi := ((104444452907/20000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((80684113857107643/4000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 (2 * hminus) 2 2 2 lmfun := by
    have heval : ((80684113857107643/4000000000000000000 : ℝ)) ≤ (((3465374481/3125000000 : ℝ)) - (0.6443107122) * ((221431186241/100000000000 : ℝ)) + (0.0647174928) * ((522202009109/100000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 (2 * hminus) 2 2 2 ((80684113857107643/4000000000000000000 : ℝ)) ((121618696107134461923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t1
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c8 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) := by
  have hS : ((10434647031/5000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((52183185673/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t16
    have hs1 := ztgcHM_t21
    have hs2 := ztgcHM_t22
    have hs3 := ztgcHM_t26
    have hs4 := ztgcHM_t30
    have hs5 := ztgcHM_t32
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((178933794511/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((357895952499/100000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((103917101337874261923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ (0.108654) * ((207845085209607923847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t21
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t16
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t16
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t26
    have hdt3 := ztgcHM_t28
    have hdt4 := ztgcHM_t27
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hprod2.1, hprod2.2, hdt3.1, hdt3.2, hdt4.1, hdt4.2, hprod5.1, hprod5.2]
  have hV : ((59119943111/50000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ volY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((11824470157/10000000000 : ℝ)) := by
    have hDm := ztgcHM_t21_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) from rfl]
    have hsD : ((141887983465829016392283/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus)) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((141887983465829016392283/10000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/1250000000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((1228867890169579548417611/6103515625000000000000 : ℝ)) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := (2 * hminus)) (y4 := 2) (y5 := 2) (y6 := (2 * hminus))
    (Vlo := ((59119943111/50000000000 : ℝ))) (Vhi := ((11824470157/10000000000 : ℝ)))
    (Slo := ((10434647031/5000000000 : ℝ))) (Shi := ((52183185673/25000000000 : ℝ)))
    (Dlo := ((178933794511/50000000000 : ℝ))) (Dhi := ((357895952499/100000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) lmfun := by
    have heval : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ (((59119943111/50000000000 : ℝ)) - (0.6443107122) * ((52183185673/25000000000 : ℝ)) + (0.0647174928) * ((178933794511/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ((8639296543178473499/125000000000000000000 : ℝ)) ((103917101337874261923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t21
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c9 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 := by
  have hS : ((114966541801/50000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((14372471163/6250000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t18
    have hs1 := ztgcHM_t20
    have hs2 := ztgcHM_t25
    have hs3 := ztgcHM_t34
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hp1, hp2]
  have hD : ((224226039097/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((112117822121/25000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((110252750616545361923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ≤ (0.108654) * ((220510749315028723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t20
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((110252750616545361923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ (0.108654) * ((220510749315028723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t18
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((110252750616545361923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ (0.108654) * ((220510749315028723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t18
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t25
    have hdt3 := ztgcHM_t25
    have hdt5 := ztgcHM_t25
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hprod2.1, hprod2.2, hdt3.1, hdt3.2, hprod4.1, hprod4.2, hdt5.1, hdt5.2]
  have hV : ((123165771067/100000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ∧ volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((123168994341/100000000000 : ℝ)) := by
    have hDm := ztgcHM_t20_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 from rfl]
    have hsD : ((147799045280427954571773/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2) ∧ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2) ≤ ((73901336604772336530871/5000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((147799045280427954571773/10000000000000000000000 : ℝ)) ^ 2 ≤ ((136528486434344232134231/625000000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((1333351450451419536331151/6103515625000000000000 : ℝ)) ≤ ((73901336604772336530871/5000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := (2 * hminus)) (y4 := 2) (y5 := (2 * hminus)) (y6 := 2)
    (Vlo := ((123165771067/100000000000 : ℝ))) (Vhi := ((123168994341/100000000000 : ℝ)))
    (Slo := ((114966541801/50000000000 : ℝ))) (Shi := ((14372471163/6250000000 : ℝ)))
    (Dlo := ((224226039097/50000000000 : ℝ))) (Dhi := ((112117822121/25000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((628604861087711779/15625000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 lmfun := by
    have heval : ((628604861087711779/15625000000000000000 : ℝ)) ≤ (((123165771067/100000000000 : ℝ)) - (0.6443107122) * ((14372471163/6250000000 : ℝ)) + (0.0647174928) * ((224226039097/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ((628604861087711779/15625000000000000000 : ℝ)) ((110252750616545361923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t20
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c10 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) := by
  have hS : ((4394492911/2000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((54940412683/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t35
    have hs1 := ztgcHM_t36
    have hs2 := ztgcHM_t37
    have hs3 := ztgcHM_t39
    have hs4 := ztgcHM_t40
    have hs5 := ztgcHM_t41
    have hs6 := ztgcHM_t43
    have hs7 := ztgcHM_t44
    have hs8 := ztgcHM_t45
    have hs9 := ztgcHM_t46
    have hs10 := ztgcHM_t48
    have hs11 := ztgcHM_t49
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((74248895423/25000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((148510158353/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t43
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((142667648658134061923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((285338562236501123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t39
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t37
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((147891111982938951923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ (0.108654) * ((295792839738049903847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t35
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t45
    have hdt3 := ztgcHM_t45
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hprod2.1, hprod2.2, hdt3.1, hdt3.2, hprod4.1, hprod4.2, hprod5.1, hprod5.2]
  have hV : ((136591223719/100000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((68298405207/50000000000 : ℝ)) := by
    have hDm := ztgcHM_t43_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) from rfl]
    have hsD : ((40977397115581602843441/2500000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((40977397115581602843441/2500000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((167927951327195450705831/625000000000000000000 : ℝ)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := (2 * hminus)) (y4 := 2) (y5 := (2 * hminus)) (y6 := (2 * hminus))
    (Vlo := ((136591223719/100000000000 : ℝ))) (Vhi := ((68298405207/50000000000 : ℝ)))
    (Slo := ((4394492911/2000000000 : ℝ))) (Shi := ((54940412683/25000000000 : ℝ)))
    (Dlo := ((74248895423/25000000000 : ℝ))) (Dhi := ((148510158353/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) lmfun := by
    have heval : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ (((136591223719/100000000000 : ℝ)) - (0.6443107122) * ((54940412683/25000000000 : ℝ)) + (0.0647174928) * ((74248895423/25000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ((17771559301751563109/125000000000000000000 : ℝ)) ((102192375318748461923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t43
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c11 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 := by
  have hS : ((10434647031/5000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((52183185673/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t17
    have hs1 := ztgcHM_t19
    have hs2 := ztgcHM_t23
    have hs3 := ztgcHM_t27
    have hs4 := ztgcHM_t28
    have hs5 := ztgcHM_t33
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((178933794511/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ ((357895952499/100000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t19
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((103917101337874261923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ≤ (0.108654) * ((207845085209607923847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t17
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t16
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t27
    have hdt4 := ztgcHM_t30
    have hdt5 := ztgcHM_t28
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hprod2.1, hprod2.2, hprod3.1, hprod3.2, hdt4.1, hdt4.2, hdt5.1, hdt5.2]
  have hV : ((59119943111/50000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ∧ volY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ≤ ((11824470157/10000000000 : ℝ)) := by
    have hDm := ztgcHM_t19_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 from rfl]
    have hsD : ((141887983465829016392283/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2) ∧ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((141887983465829016392283/10000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/1250000000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((1228867890169579548417611/6103515625000000000000 : ℝ)) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := (2 * hminus)) (y4 := (2 * hminus)) (y5 := 2) (y6 := 2)
    (Vlo := ((59119943111/50000000000 : ℝ))) (Vhi := ((11824470157/10000000000 : ℝ)))
    (Slo := ((10434647031/5000000000 : ℝ))) (Shi := ((52183185673/25000000000 : ℝ)))
    (Dlo := ((178933794511/50000000000 : ℝ))) (Dhi := ((357895952499/100000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 lmfun := by
    have heval : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ (((59119943111/50000000000 : ℝ)) - (0.6443107122) * ((52183185673/25000000000 : ℝ)) + (0.0647174928) * ((178933794511/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ((8639296543178473499/125000000000000000000 : ℝ)) ((158274604480857171923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t19
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c12 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) := by
  have hS : ((41863896917/20000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((209331345077/100000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t38
    have hs1 := ztgcHM_t42
    have hs2 := ztgcHM_t47
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hp1, hp2]
  have hD : ((24371142691/10000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ ((243737466533/100000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((137220952814990661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((274442689328030723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t42
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((137220952814990661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((274442689328030723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t38
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((137220952814990661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((274442689328030723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t38
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((137220952814990661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((274442689328030723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t38
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t47
    have hdt4 := ztgcHM_t47
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hprod2.1, hprod2.2, hprod3.1, hprod3.2, hdt4.1, hdt4.2, hprod5.1, hprod5.2]
  have hV : ((134475544087/100000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ volY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((2101208949/1562500000 : ℝ)) := by
    have hDm := ztgcHM_t42_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) from rfl]
    have hsD : ((161370772904882226933747/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus)) ≤ ((161372727282655727121283/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((161370772904882226933747/10000000000000000000000 : ℝ)) ^ 2 ≤ ((16275329/62500 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((2543081744/9765625 : ℝ)) ≤ ((161372727282655727121283/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := (2 * hminus)) (y4 := (2 * hminus)) (y5 := 2) (y6 := (2 * hminus))
    (Vlo := ((134475544087/100000000000 : ℝ))) (Vhi := ((2101208949/1562500000 : ℝ)))
    (Slo := ((41863896917/20000000000 : ℝ))) (Shi := ((209331345077/100000000000 : ℝ)))
    (Dlo := ((24371142691/10000000000 : ℝ))) (Dhi := ((243737466533/100000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((76867542854899087043/500000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) lmfun := by
    have heval : ((76867542854899087043/500000000000000000000 : ℝ)) ≤ (((134475544087/100000000000 : ℝ)) - (0.6443107122) * ((209331345077/100000000000 : ℝ)) + (0.0647174928) * ((24371142691/10000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ((76867542854899087043/500000000000000000000 : ℝ)) ((137220952814990661923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t42
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c13 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 := by
  have hS : ((4394492911/2000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((54940412683/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t35
    have hs1 := ztgcHM_t36
    have hs2 := ztgcHM_t37
    have hs3 := ztgcHM_t39
    have hs4 := ztgcHM_t40
    have hs5 := ztgcHM_t41
    have hs6 := ztgcHM_t43
    have hs7 := ztgcHM_t44
    have hs8 := ztgcHM_t45
    have hs9 := ztgcHM_t46
    have hs10 := ztgcHM_t48
    have hs11 := ztgcHM_t49
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((74248895423/25000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((148510158353/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((142667648658134061923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((285338562236501123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t41
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t40
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((147891111982938951923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ (0.108654) * ((295792839738049903847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t35
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t40
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t46
    have hdt5 := ztgcHM_t45
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hprod2.1, hprod2.2, hprod3.1, hprod3.2, hprod4.1, hprod4.2, hdt5.1, hdt5.2]
  have hV : ((136591223719/100000000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ volY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((68298405207/50000000000 : ℝ)) := by
    have hDm := ztgcHM_t41_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 from rfl]
    have hsD : ((40977397115581602843441/2500000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((40977397115581602843441/2500000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((167927951327195450705831/625000000000000000000 : ℝ)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := (2 * hminus)) (y4 := (2 * hminus)) (y5 := (2 * hminus)) (y6 := 2)
    (Vlo := ((136591223719/100000000000 : ℝ))) (Vhi := ((68298405207/50000000000 : ℝ)))
    (Slo := ((4394492911/2000000000 : ℝ))) (Shi := ((54940412683/25000000000 : ℝ)))
    (Dlo := ((74248895423/25000000000 : ℝ))) (Dhi := ((148510158353/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 lmfun := by
    have heval : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ (((136591223719/100000000000 : ℝ)) - (0.6443107122) * ((54940412683/25000000000 : ℝ)) + (0.0647174928) * ((74248895423/25000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ((17771559301751563109/125000000000000000000 : ℝ)) ((142667648658134061923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t41
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c14 : 0 < ztgMain 0 0 0 0 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) := by
  have hS : ((8768746227/4000000000 : ℝ)) ≤ solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((109618589283/50000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t50
    have hs1 := ztgcHM_t51
    have hs2 := ztgcHM_t52
    have hs3 := ztgcHM_t53
    have hs4 := ztgcHM_t54
    have hs5 := ztgcHM_t55
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((91676732711/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((36676065151/20000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t54
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t53
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t50
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((97566948881277561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((195140569317440123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t52
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t50
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt1 := ztgcHM_t55
    constructor <;> nlinarith [hprod0.1, hprod0.2, hdt1.1, hdt1.2, hprod2.1, hprod2.2, hprod3.1, hprod3.2, hprod4.1, hprod4.2, hprod5.1, hprod5.2]
  have hV : ((19344368039/12500000000 : ℝ)) ≤ volY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((38689502787/25000000000 : ℝ)) := by
    have hDm := ztgcHM_t54_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) from rfl]
    have hsD : ((92853026586905973320241/5000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((92853026586905973320241/5000000000000000000000 : ℝ)) ^ 2 ≤ ((1379469530174723/4000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((131561339804680643/381469726562500 : ℝ)) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := 2) (y3 := (2 * hminus)) (y4 := (2 * hminus)) (y5 := (2 * hminus)) (y6 := (2 * hminus))
    (Vlo := ((19344368039/12500000000 : ℝ))) (Vhi := ((38689502787/25000000000 : ℝ)))
    (Slo := ((8768746227/4000000000 : ℝ))) (Shi := ((109618589283/50000000000 : ℝ)))
    (Dlo := ((91676732711/50000000000 : ℝ))) (Dhi := ((36676065151/20000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) lmfun := by
    have heval : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ (((19344368039/12500000000 : ℝ)) - (0.6443107122) * ((109618589283/50000000000 : ℝ)) + (0.0647174928) * ((91676732711/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ((63410645569313248141/250000000000000000000 : ℝ)) ((131145528701101761923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t54
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c15 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) 2 2 2 2 := by
  have hS : ((221403382501/100000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 2 2 2 + solY (2 * hminus) 2 2 2 (2 * hminus) 2 + solY 2 2 2 (2 * hminus) (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) 2 2 ∧ solY (2 * hminus) (2 * hminus) 2 2 2 2 + solY (2 * hminus) 2 2 2 (2 * hminus) 2 + solY 2 2 2 (2 * hminus) (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((221431186241/100000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t0
    have hs1 := ztgcHM_t1
    have hs2 := ztgcHM_t3
    have hs3 := ztgcHM_t4
    have hs4 := ztgcHM_t5
    have hs5 := ztgcHM_t6
    have hs6 := ztgcHM_t8
    have hs7 := ztgcHM_t9
    have hs8 := ztgcHM_t10
    have hs9 := ztgcHM_t12
    have hs10 := ztgcHM_t13
    have hs11 := ztgcHM_t14
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((522202009109/100000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 2 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 2 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 2 (2 * hminus) ≤ ((104444452907/20000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((121618696107134461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 2 ≤ (0.108654) * ((243241018979273723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t0
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((121618696107134461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 2 2 ≤ (0.108654) * ((243241018979273723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t1
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt2 := ztgcHM_t5
    have hdt3 := ztgcHM_t13
    have hdt4 := ztgcHM_t6
    have hdt5 := ztgcHM_t8
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hdt2.1, hdt2.2, hdt3.1, hdt3.2, hdt4.1, hdt4.2, hdt5.1, hdt5.2]
  have hV : ((3465374481/3125000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) 2 2 2 2 ∧ volY (2 * hminus) (2 * hminus) 2 2 2 2 ≤ ((3465489259/3125000000 : ℝ)) := by
    have hDm := ztgcHM_t0_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) = deltaY (2 * hminus) (2 * hminus) 2 2 2 2 from rfl]
    have hsD : ((133070500070896499796033/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 2 2 2) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 2 2 2) ≤ ((4158583360817583356659/312500000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((133070500070896499796033/10000000000000000000000 : ℝ)) ^ 2 ≤ ((16887434029134686/95367431640625 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((708354684284159/4000000000000 : ℝ)) ≤ ((4158583360817583356659/312500000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := 2) (y4 := 2) (y5 := 2) (y6 := 2)
    (Vlo := ((3465374481/3125000000 : ℝ))) (Vhi := ((3465489259/3125000000 : ℝ)))
    (Slo := ((221403382501/100000000000 : ℝ))) (Shi := ((221431186241/100000000000 : ℝ)))
    (Dlo := ((522202009109/100000000000 : ℝ))) (Dhi := ((104444452907/20000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((80684113857107643/4000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) 2 2 2 2 lmfun := by
    have heval : ((80684113857107643/4000000000000000000 : ℝ)) ≤ (((3465374481/3125000000 : ℝ)) - (0.6443107122) * ((221431186241/100000000000 : ℝ)) + (0.0647174928) * ((522202009109/100000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) 2 2 2 2 ((80684113857107643/4000000000000000000 : ℝ)) ((121618696107134461923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t0
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c16 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) := by
  have hS : ((114966541801/50000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + solY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ solY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + solY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((14372471163/6250000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t18
    have hs1 := ztgcHM_t20
    have hs2 := ztgcHM_t25
    have hs3 := ztgcHM_t34
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hp1, hp2]
  have hD : ((224226039097/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ ((112117822121/25000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((110252750616545361923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ (0.108654) * ((220510749315028723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t18
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((110252750616545361923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) 2 ≤ (0.108654) * ((220510749315028723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t20
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((110252750616545361923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ (0.108654) * ((220510749315028723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t18
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt2 := ztgcHM_t25
    have hdt3 := ztgcHM_t34
    have hdt4 := ztgcHM_t25
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hdt2.1, hdt2.2, hdt3.1, hdt3.2, hdt4.1, hdt4.2, hprod5.1, hprod5.2]
  have hV : ((123165771067/100000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ volY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ ((123168994341/100000000000 : ℝ)) := by
    have hDm := ztgcHM_t18_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) from rfl]
    have hsD : ((147799045280427954571773/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus)) ≤ ((73901336604772336530871/5000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((147799045280427954571773/10000000000000000000000 : ℝ)) ^ 2 ≤ ((136528486434344232134231/625000000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((1333351450451419536331151/6103515625000000000000 : ℝ)) ≤ ((73901336604772336530871/5000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := 2) (y4 := 2) (y5 := 2) (y6 := (2 * hminus))
    (Vlo := ((123165771067/100000000000 : ℝ))) (Vhi := ((123168994341/100000000000 : ℝ)))
    (Slo := ((114966541801/50000000000 : ℝ))) (Shi := ((14372471163/6250000000 : ℝ)))
    (Dlo := ((224226039097/50000000000 : ℝ))) (Dhi := ((112117822121/25000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((628604861087711779/15625000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) lmfun := by
    have heval : ((628604861087711779/15625000000000000000 : ℝ)) ≤ (((123165771067/100000000000 : ℝ)) - (0.6443107122) * ((14372471163/6250000000 : ℝ)) + (0.0647174928) * ((224226039097/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ((628604861087711779/15625000000000000000 : ℝ)) ((110252750616545361923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t18
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c17 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 := by
  have hS : ((10434647031/5000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ solY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ ((52183185673/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t17
    have hs1 := ztgcHM_t19
    have hs2 := ztgcHM_t23
    have hs3 := ztgcHM_t27
    have hs4 := ztgcHM_t28
    have hs5 := ztgcHM_t33
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((178933794511/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((357895952499/100000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((103917101337874261923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ≤ (0.108654) * ((207845085209607923847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t17
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t19
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t16
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt2 := ztgcHM_t27
    have hdt3 := ztgcHM_t32
    have hdt5 := ztgcHM_t27
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hdt2.1, hdt2.2, hdt3.1, hdt3.2, hprod4.1, hprod4.2, hdt5.1, hdt5.2]
  have hV : ((59119943111/50000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ∧ volY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ≤ ((11824470157/10000000000 : ℝ)) := by
    have hDm := ztgcHM_t17_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 from rfl]
    have hsD : ((141887983465829016392283/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((141887983465829016392283/10000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/1250000000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((1228867890169579548417611/6103515625000000000000 : ℝ)) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := 2) (y4 := 2) (y5 := (2 * hminus)) (y6 := 2)
    (Vlo := ((59119943111/50000000000 : ℝ))) (Vhi := ((11824470157/10000000000 : ℝ)))
    (Slo := ((10434647031/5000000000 : ℝ))) (Shi := ((52183185673/25000000000 : ℝ)))
    (Dlo := ((178933794511/50000000000 : ℝ))) (Dhi := ((357895952499/100000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 lmfun := by
    have heval : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ (((59119943111/50000000000 : ℝ)) - (0.6443107122) * ((52183185673/25000000000 : ℝ)) + (0.0647174928) * ((178933794511/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) 2 ((8639296543178473499/125000000000000000000 : ℝ)) ((103917101337874261923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t17
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c18 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) := by
  have hS : ((4394492911/2000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ solY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((54940412683/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t35
    have hs1 := ztgcHM_t36
    have hs2 := ztgcHM_t37
    have hs3 := ztgcHM_t39
    have hs4 := ztgcHM_t40
    have hs5 := ztgcHM_t41
    have hs6 := ztgcHM_t43
    have hs7 := ztgcHM_t44
    have hs8 := ztgcHM_t45
    have hs9 := ztgcHM_t46
    have hs10 := ztgcHM_t48
    have hs11 := ztgcHM_t49
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((74248895423/25000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((148510158353/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t40
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((142667648658134061923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((285338562236501123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t41
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((147891111982938951923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ (0.108654) * ((295792839738049903847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t35
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t37
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt2 := ztgcHM_t46
    have hdt3 := ztgcHM_t49
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hdt2.1, hdt2.2, hdt3.1, hdt3.2, hprod4.1, hprod4.2, hprod5.1, hprod5.2]
  have hV : ((136591223719/100000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ ((68298405207/50000000000 : ℝ)) := by
    have hDm := ztgcHM_t40_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) from rfl]
    have hsD : ((40977397115581602843441/2500000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((40977397115581602843441/2500000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((167927951327195450705831/625000000000000000000 : ℝ)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := 2) (y4 := 2) (y5 := (2 * hminus)) (y6 := (2 * hminus))
    (Vlo := ((136591223719/100000000000 : ℝ))) (Vhi := ((68298405207/50000000000 : ℝ)))
    (Slo := ((4394492911/2000000000 : ℝ))) (Shi := ((54940412683/25000000000 : ℝ)))
    (Dlo := ((74248895423/25000000000 : ℝ))) (Dhi := ((148510158353/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) lmfun := by
    have heval : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ (((136591223719/100000000000 : ℝ)) - (0.6443107122) * ((54940412683/25000000000 : ℝ)) + (0.0647174928) * ((74248895423/25000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ((17771559301751563109/125000000000000000000 : ℝ)) ((102192375318748461923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t40
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c19 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 := by
  have hS : ((10434647031/5000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((52183185673/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t16
    have hs1 := ztgcHM_t21
    have hs2 := ztgcHM_t22
    have hs3 := ztgcHM_t26
    have hs4 := ztgcHM_t30
    have hs5 := ztgcHM_t32
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((178933794511/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ ((357895952499/100000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t16
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((103917101337874261923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ (0.108654) * ((207845085209607923847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t21
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((158274604480857171923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((316552782986764583847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t23
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt2 := ztgcHM_t26
    have hdt4 := ztgcHM_t28
    have hdt5 := ztgcHM_t30
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hdt2.1, hdt2.2, hprod3.1, hprod3.2, hdt4.1, hdt4.2, hdt5.1, hdt5.2]
  have hV : ((59119943111/50000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ∧ volY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ≤ ((11824470157/10000000000 : ℝ)) := by
    have hDm := ztgcHM_t16_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 from rfl]
    have hsD : ((141887983465829016392283/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((141887983465829016392283/10000000000000000000000 : ℝ)) ^ 2 ≤ ((251652498653295719514337/1250000000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((1228867890169579548417611/6103515625000000000000 : ℝ)) ≤ ((141893521884566521742673/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := 2) (y4 := (2 * hminus)) (y5 := 2) (y6 := 2)
    (Vlo := ((59119943111/50000000000 : ℝ))) (Vhi := ((11824470157/10000000000 : ℝ)))
    (Slo := ((10434647031/5000000000 : ℝ))) (Shi := ((52183185673/25000000000 : ℝ)))
    (Dlo := ((178933794511/50000000000 : ℝ))) (Dhi := ((357895952499/100000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 lmfun := by
    have heval : ((8639296543178473499/125000000000000000000 : ℝ)) ≤ (((59119943111/50000000000 : ℝ)) - (0.6443107122) * ((52183185673/25000000000 : ℝ)) + (0.0647174928) * ((178933794511/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 2 ((8639296543178473499/125000000000000000000 : ℝ)) ((158274604480857171923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t16
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c20 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) := by
  have hS : ((4394492911/2000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((54940412683/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t35
    have hs1 := ztgcHM_t36
    have hs2 := ztgcHM_t37
    have hs3 := ztgcHM_t39
    have hs4 := ztgcHM_t40
    have hs5 := ztgcHM_t41
    have hs6 := ztgcHM_t43
    have hs7 := ztgcHM_t44
    have hs8 := ztgcHM_t45
    have hs9 := ztgcHM_t46
    have hs10 := ztgcHM_t48
    have hs11 := ztgcHM_t49
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((74248895423/25000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ ((148510158353/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((142667648658134061923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((285338562236501123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t39
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t43
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((147891111982938951923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((295792839738049903847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t44
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t40
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt2 := ztgcHM_t45
    have hdt4 := ztgcHM_t45
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hdt2.1, hdt2.2, hprod3.1, hprod3.2, hdt4.1, hdt4.2, hprod5.1, hprod5.2]
  have hV : ((136591223719/100000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ volY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((68298405207/50000000000 : ℝ)) := by
    have hDm := ztgcHM_t39_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) from rfl]
    have hsD : ((40977397115581602843441/2500000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((40977397115581602843441/2500000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((167927951327195450705831/625000000000000000000 : ℝ)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := 2) (y4 := (2 * hminus)) (y5 := 2) (y6 := (2 * hminus))
    (Vlo := ((136591223719/100000000000 : ℝ))) (Vhi := ((68298405207/50000000000 : ℝ)))
    (Slo := ((4394492911/2000000000 : ℝ))) (Shi := ((54940412683/25000000000 : ℝ)))
    (Dlo := ((74248895423/25000000000 : ℝ))) (Dhi := ((148510158353/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) lmfun := by
    have heval : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ (((136591223719/100000000000 : ℝ)) - (0.6443107122) * ((54940412683/25000000000 : ℝ)) + (0.0647174928) * ((74248895423/25000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ((17771559301751563109/125000000000000000000 : ℝ)) ((142667648658134061923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t39
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c21 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 := by
  have hS : ((41863896917/20000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ ((209331345077/100000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t38
    have hs1 := ztgcHM_t42
    have hs2 := ztgcHM_t47
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hp1, hp2]
  have hD : ((24371142691/10000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((243737466533/100000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((137220952814990661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((274442689328030723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t38
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((137220952814990661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((274442689328030723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t42
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((137220952814990661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((274442689328030723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t42
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((137220952814990661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((274442689328030723847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t38
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt2 := ztgcHM_t47
    have hdt5 := ztgcHM_t47
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hdt2.1, hdt2.2, hprod3.1, hprod3.2, hprod4.1, hprod4.2, hdt5.1, hdt5.2]
  have hV : ((134475544087/100000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ∧ volY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ≤ ((2101208949/1562500000 : ℝ)) := by
    have hDm := ztgcHM_t38_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 from rfl]
    have hsD : ((161370772904882226933747/10000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2) ≤ ((161372727282655727121283/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((161370772904882226933747/10000000000000000000000 : ℝ)) ^ 2 ≤ ((16275329/62500 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((2543081744/9765625 : ℝ)) ≤ ((161372727282655727121283/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := 2) (y4 := (2 * hminus)) (y5 := (2 * hminus)) (y6 := 2)
    (Vlo := ((134475544087/100000000000 : ℝ))) (Vhi := ((2101208949/1562500000 : ℝ)))
    (Slo := ((41863896917/20000000000 : ℝ))) (Shi := ((209331345077/100000000000 : ℝ)))
    (Dlo := ((24371142691/10000000000 : ℝ))) (Dhi := ((243737466533/100000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((76867542854899087043/500000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 lmfun := by
    have heval : ((76867542854899087043/500000000000000000000 : ℝ)) ≤ (((134475544087/100000000000 : ℝ)) - (0.6443107122) * ((209331345077/100000000000 : ℝ)) + (0.0647174928) * ((24371142691/10000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) 2 ((76867542854899087043/500000000000000000000 : ℝ)) ((137220952814990661923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t38
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c22 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) := by
  have hS : ((8768746227/4000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((109618589283/50000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t50
    have hs1 := ztgcHM_t51
    have hs2 := ztgcHM_t52
    have hs3 := ztgcHM_t53
    have hs4 := ztgcHM_t54
    have hs5 := ztgcHM_t55
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((91676732711/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((36676065151/20000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t53
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t54
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t54
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t50
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((97566948881277561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((195140569317440123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t52
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt2 := ztgcHM_t55
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hdt2.1, hdt2.2, hprod3.1, hprod3.2, hprod4.1, hprod4.2, hprod5.1, hprod5.2]
  have hV : ((19344368039/12500000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((38689502787/25000000000 : ℝ)) := by
    have hDm := ztgcHM_t53_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) from rfl]
    have hsD : ((92853026586905973320241/5000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((92853026586905973320241/5000000000000000000000 : ℝ)) ^ 2 ≤ ((1379469530174723/4000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((131561339804680643/381469726562500 : ℝ)) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := 2) (y4 := (2 * hminus)) (y5 := (2 * hminus)) (y6 := (2 * hminus))
    (Vlo := ((19344368039/12500000000 : ℝ))) (Vhi := ((38689502787/25000000000 : ℝ)))
    (Slo := ((8768746227/4000000000 : ℝ))) (Shi := ((109618589283/50000000000 : ℝ)))
    (Dlo := ((91676732711/50000000000 : ℝ))) (Dhi := ((36676065151/20000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) lmfun := by
    have heval : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ (((19344368039/12500000000 : ℝ)) - (0.6443107122) * ((109618589283/50000000000 : ℝ)) + (0.0647174928) * ((91676732711/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ((63410645569313248141/250000000000000000000 : ℝ)) ((131145528701101761923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t53
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c23 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 := by
  have hS : ((899645979/400000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + solY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + solY (2 * hminus) 2 2 2 (2 * hminus) (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((224922677263/100000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t15
    have hs1 := ztgcHM_t24
    have hs2 := ztgcHM_t29
    have hs3 := ztgcHM_t31
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hp1, hp2]
  have hD : ((431163651191/100000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((215589342647/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((115778844869647661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ≤ (0.108654) * ((231560833507112523847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t15
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((115778844869647661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ≤ (0.108654) * ((231560833507112523847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t15
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((115778844869647661923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ≤ (0.108654) * ((231560833507112523847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t15
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt3 := ztgcHM_t29
    have hdt4 := ztgcHM_t29
    have hdt5 := ztgcHM_t29
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hprod2.1, hprod2.2, hdt3.1, hdt3.2, hdt4.1, hdt4.2, hdt5.1, hdt5.2]
  have hV : ((125638255439/100000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ∧ volY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ≤ ((125639762879/100000000000 : ℝ)) := by
    have hDm := ztgcHM_t15_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 from rfl]
    have hsD : ((1507660265263339733229/100000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2) ≤ ((150767595455328595304561/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((1507660265263339733229/100000000000000000000 : ℝ)) ^ 2 ≤ ((56825987/250000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((2219811308/9765625 : ℝ)) ≤ ((150767595455328595304561/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := (2 * hminus)) (y4 := 2) (y5 := 2) (y6 := 2)
    (Vlo := ((125638255439/100000000000 : ℝ))) (Vhi := ((125639762879/100000000000 : ℝ)))
    (Slo := ((899645979/400000000 : ℝ))) (Shi := ((224922677263/100000000000 : ℝ)))
    (Dlo := ((431163651191/100000000000 : ℝ))) (Dhi := ((215589342647/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((43109977766604886081/500000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 lmfun := by
    have heval : ((43109977766604886081/500000000000000000000 : ℝ)) ≤ (((125638255439/100000000000 : ℝ)) - (0.6443107122) * ((224922677263/100000000000 : ℝ)) + (0.0647174928) * ((431163651191/100000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 2 ((43109977766604886081/500000000000000000000 : ℝ)) ((115778844869647661923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t15
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c24 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) := by
  have hS : ((4394492911/2000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY 2 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((54940412683/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t35
    have hs1 := ztgcHM_t36
    have hs2 := ztgcHM_t37
    have hs3 := ztgcHM_t39
    have hs4 := ztgcHM_t40
    have hs5 := ztgcHM_t41
    have hs6 := ztgcHM_t43
    have hs7 := ztgcHM_t44
    have hs8 := ztgcHM_t45
    have hs9 := ztgcHM_t46
    have hs10 := ztgcHM_t48
    have hs11 := ztgcHM_t49
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((74248895423/25000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((148510158353/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t37
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t36
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((147891111982938951923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ (0.108654) * ((295792839738049903847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t35
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((142667648658134061923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((285338562236501123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t39
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt3 := ztgcHM_t48
    have hdt4 := ztgcHM_t46
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hprod2.1, hprod2.2, hdt3.1, hdt3.2, hdt4.1, hdt4.2, hprod5.1, hprod5.2]
  have hV : ((136591223719/100000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ volY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((68298405207/50000000000 : ℝ)) := by
    have hDm := ztgcHM_t37_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) from rfl]
    have hsD : ((40977397115581602843441/2500000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((40977397115581602843441/2500000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((167927951327195450705831/625000000000000000000 : ℝ)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := (2 * hminus)) (y4 := 2) (y5 := 2) (y6 := (2 * hminus))
    (Vlo := ((136591223719/100000000000 : ℝ))) (Vhi := ((68298405207/50000000000 : ℝ)))
    (Slo := ((4394492911/2000000000 : ℝ))) (Shi := ((54940412683/25000000000 : ℝ)))
    (Dlo := ((74248895423/25000000000 : ℝ))) (Dhi := ((148510158353/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) lmfun := by
    have heval : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ (((136591223719/100000000000 : ℝ)) - (0.6443107122) * ((54940412683/25000000000 : ℝ)) + (0.0647174928) * ((74248895423/25000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ((17771559301751563109/125000000000000000000 : ℝ)) ((102192375318748461923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t37
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c25 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 := by
  have hS : ((4394492911/2000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((54940412683/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t35
    have hs1 := ztgcHM_t36
    have hs2 := ztgcHM_t37
    have hs3 := ztgcHM_t39
    have hs4 := ztgcHM_t40
    have hs5 := ztgcHM_t41
    have hs6 := ztgcHM_t43
    have hs7 := ztgcHM_t44
    have hs8 := ztgcHM_t45
    have hs9 := ztgcHM_t46
    have hs10 := ztgcHM_t48
    have hs11 := ztgcHM_t49
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((74248895423/25000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((148510158353/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t36
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((147891111982938951923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ (0.108654) * ((295792839738049903847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t35
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t37
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((142667648658134061923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((285338562236501123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t39
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt3 := ztgcHM_t46
    have hdt5 := ztgcHM_t46
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hprod2.1, hprod2.2, hdt3.1, hdt3.2, hprod4.1, hprod4.2, hdt5.1, hdt5.2]
  have hV : ((136591223719/100000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ volY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ ((68298405207/50000000000 : ℝ)) := by
    have hDm := ztgcHM_t36_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) (2 * 2) = deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 from rfl]
    have hsD : ((40977397115581602843441/2500000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((40977397115581602843441/2500000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((167927951327195450705831/625000000000000000000 : ℝ)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := (2 * hminus)) (y4 := 2) (y5 := (2 * hminus)) (y6 := 2)
    (Vlo := ((136591223719/100000000000 : ℝ))) (Vhi := ((68298405207/50000000000 : ℝ)))
    (Slo := ((4394492911/2000000000 : ℝ))) (Shi := ((54940412683/25000000000 : ℝ)))
    (Dlo := ((74248895423/25000000000 : ℝ))) (Dhi := ((148510158353/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 lmfun := by
    have heval : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ (((136591223719/100000000000 : ℝ)) - (0.6443107122) * ((54940412683/25000000000 : ℝ)) + (0.0647174928) * ((74248895423/25000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ((17771559301751563109/125000000000000000000 : ℝ)) ((102192375318748461923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t36
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c26 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) := by
  have hS : ((8768746227/4000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((109618589283/50000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t50
    have hs1 := ztgcHM_t51
    have hs2 := ztgcHM_t52
    have hs3 := ztgcHM_t53
    have hs4 := ztgcHM_t54
    have hs5 := ztgcHM_t55
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((91676732711/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((36676065151/20000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((97566948881277561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((195140569317440123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t52
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t50
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t51
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t51
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t51
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt3 := ztgcHM_t55
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hprod2.1, hprod2.2, hdt3.1, hdt3.2, hprod4.1, hprod4.2, hprod5.1, hprod5.2]
  have hV : ((19344368039/12500000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ ((38689502787/25000000000 : ℝ)) := by
    have hDm := ztgcHM_t52_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) from rfl]
    have hsD : ((92853026586905973320241/5000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus)) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((92853026586905973320241/5000000000000000000000 : ℝ)) ^ 2 ≤ ((1379469530174723/4000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((131561339804680643/381469726562500 : ℝ)) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := (2 * hminus)) (y4 := 2) (y5 := (2 * hminus)) (y6 := (2 * hminus))
    (Vlo := ((19344368039/12500000000 : ℝ))) (Vhi := ((38689502787/25000000000 : ℝ)))
    (Slo := ((8768746227/4000000000 : ℝ))) (Shi := ((109618589283/50000000000 : ℝ)))
    (Dlo := ((91676732711/50000000000 : ℝ))) (Dhi := ((36676065151/20000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) lmfun := by
    have heval : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ (((19344368039/12500000000 : ℝ)) - (0.6443107122) * ((109618589283/50000000000 : ℝ)) + (0.0647174928) * ((91676732711/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ((63410645569313248141/250000000000000000000 : ℝ)) ((97566948881277561923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t52
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c27 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 := by
  have hS : ((4394492911/2000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + solY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((54940412683/25000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t35
    have hs1 := ztgcHM_t36
    have hs2 := ztgcHM_t37
    have hs3 := ztgcHM_t39
    have hs4 := ztgcHM_t40
    have hs5 := ztgcHM_t41
    have hs6 := ztgcHM_t43
    have hs7 := ztgcHM_t44
    have hs8 := ztgcHM_t45
    have hs9 := ztgcHM_t46
    have hs10 := ztgcHM_t48
    have hs11 := ztgcHM_t49
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hs6.1, hs6.2, hs7.1, hs7.2, hs8.1, hs8.2, hs9.1, hs9.2, hs10.1, hs10.2, hs11.1, hs11.2, hp1, hp2]
  have hD : ((74248895423/25000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((148510158353/50000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((147891111982938951923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ (0.108654) * ((295792839738049903847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t35
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t37
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((102192375318748461923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ (0.108654) * ((204392586117475123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t36
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((142667648658134061923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((285338562236501123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t39
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt4 := ztgcHM_t48
    have hdt5 := ztgcHM_t48
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hprod2.1, hprod2.2, hprod3.1, hprod3.2, hdt4.1, hdt4.2, hdt5.1, hdt5.2]
  have hV : ((136591223719/100000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ∧ volY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ≤ ((68298405207/50000000000 : ℝ)) := by
    have hDm := ztgcHM_t35_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) (2 * 2) = deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 from rfl]
    have hsD : ((40977397115581602843441/2500000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((40977397115581602843441/2500000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((167927951327195450705831/625000000000000000000 : ℝ)) ≤ ((32783210499332210466549/2000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := (2 * hminus)) (y4 := (2 * hminus)) (y5 := 2) (y6 := 2)
    (Vlo := ((136591223719/100000000000 : ℝ))) (Vhi := ((68298405207/50000000000 : ℝ)))
    (Slo := ((4394492911/2000000000 : ℝ))) (Shi := ((54940412683/25000000000 : ℝ)))
    (Dlo := ((74248895423/25000000000 : ℝ))) (Dhi := ((148510158353/50000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 lmfun := by
    have heval : ((17771559301751563109/125000000000000000000 : ℝ)) ≤ (((136591223719/100000000000 : ℝ)) - (0.6443107122) * ((54940412683/25000000000 : ℝ)) + (0.0647174928) * ((74248895423/25000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 2 ((17771559301751563109/125000000000000000000 : ℝ)) ((147891111982938951923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t35
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c28 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) := by
  have hS : ((8768746227/4000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((109618589283/50000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t50
    have hs1 := ztgcHM_t51
    have hs2 := ztgcHM_t52
    have hs3 := ztgcHM_t53
    have hs4 := ztgcHM_t54
    have hs5 := ztgcHM_t55
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((91676732711/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((36676065151/20000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t51
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((97566948881277561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((195140569317440123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t52
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t50
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t53
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t53
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt4 := ztgcHM_t55
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hprod2.1, hprod2.2, hprod3.1, hprod3.2, hdt4.1, hdt4.2, hprod5.1, hprod5.2]
  have hV : ((19344368039/12500000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ volY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ ((38689502787/25000000000 : ℝ)) := by
    have hDm := ztgcHM_t51_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) from rfl]
    have hsD : ((92853026586905973320241/5000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus)) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((92853026586905973320241/5000000000000000000000 : ℝ)) ^ 2 ≤ ((1379469530174723/4000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((131561339804680643/381469726562500 : ℝ)) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := (2 * hminus)) (y4 := (2 * hminus)) (y5 := 2) (y6 := (2 * hminus))
    (Vlo := ((19344368039/12500000000 : ℝ))) (Vhi := ((38689502787/25000000000 : ℝ)))
    (Slo := ((8768746227/4000000000 : ℝ))) (Shi := ((109618589283/50000000000 : ℝ)))
    (Dlo := ((91676732711/50000000000 : ℝ))) (Dhi := ((36676065151/20000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) lmfun := by
    have heval : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ (((19344368039/12500000000 : ℝ)) - (0.6443107122) * ((109618589283/50000000000 : ℝ)) + (0.0647174928) * ((91676732711/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ((63410645569313248141/250000000000000000000 : ℝ)) ((131145528701101761923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t51
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c29 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 := by
  have hS : ((8768746227/4000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + solY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((109618589283/50000000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t50
    have hs1 := ztgcHM_t51
    have hs2 := ztgcHM_t52
    have hs3 := ztgcHM_t53
    have hs4 := ztgcHM_t54
    have hs5 := ztgcHM_t55
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2, hs4.1, hs4.2, hs5.1, hs5.2, hp1, hp2]
  have hD : ((91676732711/50000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) + lmfun (2 / 2) * dihY 2 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((36676065151/20000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    have hlone : lmfun (2 / 2) = 1 := by norm_num [lmfun, h0]
    rw [hslot, hlone]
    have hprod0 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t50
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t51
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((97566948881277561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) ≤ (0.108654) * ((195140569317440123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t52
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t51
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((131145528701101761923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((262293184294343323847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t53
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hdt5 := ztgcHM_t55
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hprod2.1, hprod2.2, hprod3.1, hprod3.2, hprod4.1, hprod4.2, hdt5.1, hdt5.2]
  have hV : ((19344368039/12500000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ∧ volY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ≤ ((38689502787/25000000000 : ℝ)) := by
    have hDm := ztgcHM_t50_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) (2 * 2) = deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 from rfl]
    have hsD : ((92853026586905973320241/5000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((92853026586905973320241/5000000000000000000000 : ℝ)) ^ 2 ≤ ((1379469530174723/4000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((131561339804680643/381469726562500 : ℝ)) ≤ ((185709493378056493192347/10000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := (2 * hminus)) (y4 := (2 * hminus)) (y5 := (2 * hminus)) (y6 := 2)
    (Vlo := ((19344368039/12500000000 : ℝ))) (Vhi := ((38689502787/25000000000 : ℝ)))
    (Slo := ((8768746227/4000000000 : ℝ))) (Shi := ((109618589283/50000000000 : ℝ)))
    (Dlo := ((91676732711/50000000000 : ℝ))) (Dhi := ((36676065151/20000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 lmfun := by
    have heval : ((63410645569313248141/250000000000000000000 : ℝ)) ≤ (((19344368039/12500000000 : ℝ)) - (0.6443107122) * ((109618589283/50000000000 : ℝ)) + (0.0647174928) * ((91676732711/50000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) 2 ((63410645569313248141/250000000000000000000 : ℝ)) ((131145528701101761923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t50
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

theorem ztgcHM_c30 : 0 < ztgMain 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) := by
  have hS : ((220501888533/100000000000 : ℝ)) ≤ solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + solY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((13782911869/6250000000 : ℝ)) := by
    simp only [solY]
    have hs0 := ztgcHM_t56
    obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
    constructor <;> linarith [hs0.1, hs0.2, hp1, hp2]
  have hD : ((401098144781/500000000000 : ℝ)) ≤ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) + lmfun ((2 * hminus) / 2) * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((802499642537/1000000000000 : ℝ)) := by
    have hslot : (2 * hminus) / 2 = hminus := by ring
    rw [hslot]
    have hprod0 : (0.108615) * ((123094920830703561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((246193925223346123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t56
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod1 : (0.108615) * ((123094920830703561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((246193925223346123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t56
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod2 : (0.108615) * ((123094920830703561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((246193925223346123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t56
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod3 : (0.108615) * ((123094920830703561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((246193925223346123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t56
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod4 : (0.108615) * ((123094920830703561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((246193925223346123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t56
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    have hprod5 : (0.108615) * ((123094920830703561923/100000000000000000000 : ℝ)) ≤ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ lmfun hminus * dihY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ (0.108654) * ((246193925223346123847/200000000000000000000 : ℝ)) := by
      have hlm := ztg_lmfun_hminus_bounds
      have hd := ztgcHM_t56
      exact ⟨mul_le_mul hlm.1 hd.1 (by linarith [hlm.1]) (by linarith [hd.1]), mul_le_mul hlm.2 hd.2 (by linarith [hlm.1]) (by linarith [hd.1])⟩
    constructor <;> nlinarith [hprod0.1, hprod0.2, hprod1.1, hprod1.2, hprod2.1, hprod2.2, hprod3.1, hprod3.2, hprod4.1, hprod4.2, hprod5.1, hprod5.2]
  have hV : ((35238807267/20000000000 : ℝ)) ≤ volY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ∧ volY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((35239705607/20000000000 : ℝ)) := by
    have hDm := ztgcHM_t56_delta
    unfold volY volXf
    rw [show deltaX ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) ((2 * hminus) * (2 * hminus)) = deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) from rfl]
    have hsD : ((105716481800930518093353/5000000000000000000000 : ℝ)) ≤ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ∧ Real.sqrt (deltaY (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus)) ≤ ((105719056820732056715013/5000000000000000000000 : ℝ)) := ztg_sqrt_bounds (by norm_num) (by norm_num) (le_trans (by norm_num : ((105716481800930518093353/5000000000000000000000 : ℝ)) ^ 2 ≤ ((14305247419799561436289/32000000000000000000 : ℝ))) hDm.1) (le_trans hDm.2 (by norm_num : ((13323448840036601566947529/29802322387695312500000 : ℝ)) ≤ ((105719056820732056715013/5000000000000000000000 : ℝ)) ^ 2))
    constructor <;> linarith [hsD.1, hsD.2]
  have h4k := g4v_corner_value_bounds (y1 := 2 * hminus) (y2 := (2 * hminus)) (y3 := (2 * hminus)) (y4 := (2 * hminus)) (y5 := (2 * hminus)) (y6 := (2 * hminus))
    (Vlo := ((35238807267/20000000000 : ℝ))) (Vhi := ((35239705607/20000000000 : ℝ)))
    (Slo := ((220501888533/100000000000 : ℝ))) (Shi := ((13782911869/6250000000 : ℝ)))
    (Dlo := ((401098144781/500000000000 : ℝ))) (Dhi := ((802499642537/1000000000000 : ℝ)))
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    hV hS hD ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hG : ((122806266857212423083/312500000000000000000 : ℝ)) ≤ gamma4fgcy (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) lmfun := by
    have heval : ((122806266857212423083/312500000000000000000 : ℝ)) ≤ (((35238807267/20000000000 : ℝ)) - (0.6443107122) * ((13782911869/6250000000 : ℝ)) + (0.0647174928) * ((401098144781/500000000000 : ℝ))) := by norm_num
    linarith [h4k.1, heval]
  refine ztg_main_pos_of_gD 0 0 0 0 (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) (2 * hminus) ((122806266857212423083/312500000000000000000 : ℝ)) ((123094920830703561923/100000000000000000000 : ℝ)) ?_ ?_ ?_
  · exact hG
  · have hdm := ztgcHM_t56
    linarith
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]


/-! ## Axiom audit (house style) -/

#print axioms ztgcHM_f0
#print axioms ztgcHM_f1
#print axioms ztgcHM_f2
#print axioms ztgcHM_f3
#print axioms ztgcHM_f4
#print axioms ztgcHM_f5
#print axioms ztgcHM_f6
#print axioms ztgcHM_f7
#print axioms ztgcHM_f8
#print axioms ztgcHM_f9
#print axioms ztgcHM_f10
#print axioms ztgcHM_f11
#print axioms ztgcHM_f12
#print axioms ztgcHM_f13
#print axioms ztgcHM_f14
#print axioms ztgcHM_f15
#print axioms ztgcHM_f16
#print axioms ztgcHM_t0_delta
#print axioms ztgcHM_t0
#print axioms ztgcHM_t1_delta
#print axioms ztgcHM_t1
#print axioms ztgcHM_t2_delta
#print axioms ztgcHM_t2
#print axioms ztgcHM_t3_delta
#print axioms ztgcHM_t3
#print axioms ztgcHM_t4_delta
#print axioms ztgcHM_t4
#print axioms ztgcHM_t5_delta
#print axioms ztgcHM_t5
#print axioms ztgcHM_t6_delta
#print axioms ztgcHM_t6
#print axioms ztgcHM_t7_delta
#print axioms ztgcHM_t7
#print axioms ztgcHM_t8_delta
#print axioms ztgcHM_t8
#print axioms ztgcHM_t9_delta
#print axioms ztgcHM_t9
#print axioms ztgcHM_t10_delta
#print axioms ztgcHM_t10
#print axioms ztgcHM_t11_delta
#print axioms ztgcHM_t11
#print axioms ztgcHM_t12_delta
#print axioms ztgcHM_t12
#print axioms ztgcHM_t13_delta
#print axioms ztgcHM_t13
#print axioms ztgcHM_t14_delta
#print axioms ztgcHM_t14
#print axioms ztgcHM_t15_delta
#print axioms ztgcHM_t15
#print axioms ztgcHM_t16_delta
#print axioms ztgcHM_t16
#print axioms ztgcHM_t17_delta
#print axioms ztgcHM_t17
#print axioms ztgcHM_t18_delta
#print axioms ztgcHM_t18
#print axioms ztgcHM_t19_delta
#print axioms ztgcHM_t19
#print axioms ztgcHM_t20_delta
#print axioms ztgcHM_t20
#print axioms ztgcHM_t21_delta
#print axioms ztgcHM_t21
#print axioms ztgcHM_t22_delta
#print axioms ztgcHM_t22
#print axioms ztgcHM_t23_delta
#print axioms ztgcHM_t23
#print axioms ztgcHM_t24_delta
#print axioms ztgcHM_t24
#print axioms ztgcHM_t25_delta
#print axioms ztgcHM_t25
#print axioms ztgcHM_t26_delta
#print axioms ztgcHM_t26
#print axioms ztgcHM_t27_delta
#print axioms ztgcHM_t27
#print axioms ztgcHM_t28_delta
#print axioms ztgcHM_t28
#print axioms ztgcHM_t29_delta
#print axioms ztgcHM_t29
#print axioms ztgcHM_t30_delta
#print axioms ztgcHM_t30
#print axioms ztgcHM_t31_delta
#print axioms ztgcHM_t31
#print axioms ztgcHM_t32_delta
#print axioms ztgcHM_t32
#print axioms ztgcHM_t33_delta
#print axioms ztgcHM_t33
#print axioms ztgcHM_t34_delta
#print axioms ztgcHM_t34
#print axioms ztgcHM_t35_delta
#print axioms ztgcHM_t35
#print axioms ztgcHM_t36_delta
#print axioms ztgcHM_t36
#print axioms ztgcHM_t37_delta
#print axioms ztgcHM_t37
#print axioms ztgcHM_t38_delta
#print axioms ztgcHM_t38
#print axioms ztgcHM_t39_delta
#print axioms ztgcHM_t39
#print axioms ztgcHM_t40_delta
#print axioms ztgcHM_t40
#print axioms ztgcHM_t41_delta
#print axioms ztgcHM_t41
#print axioms ztgcHM_t42_delta
#print axioms ztgcHM_t42
#print axioms ztgcHM_t43_delta
#print axioms ztgcHM_t43
#print axioms ztgcHM_t44_delta
#print axioms ztgcHM_t44
#print axioms ztgcHM_t45_delta
#print axioms ztgcHM_t45
#print axioms ztgcHM_t46_delta
#print axioms ztgcHM_t46
#print axioms ztgcHM_t47_delta
#print axioms ztgcHM_t47
#print axioms ztgcHM_t48_delta
#print axioms ztgcHM_t48
#print axioms ztgcHM_t49_delta
#print axioms ztgcHM_t49
#print axioms ztgcHM_t50_delta
#print axioms ztgcHM_t50
#print axioms ztgcHM_t51_delta
#print axioms ztgcHM_t51
#print axioms ztgcHM_t52_delta
#print axioms ztgcHM_t52
#print axioms ztgcHM_t53_delta
#print axioms ztgcHM_t53
#print axioms ztgcHM_t54_delta
#print axioms ztgcHM_t54
#print axioms ztgcHM_t55_delta
#print axioms ztgcHM_t55
#print axioms ztgcHM_t56_delta
#print axioms ztgcHM_t56
#print axioms ztgcHM_c0
#print axioms ztgcHM_c1
#print axioms ztgcHM_c2
#print axioms ztgcHM_c3
#print axioms ztgcHM_c4
#print axioms ztgcHM_c5
#print axioms ztgcHM_c6
#print axioms ztgcHM_c7
#print axioms ztgcHM_c8
#print axioms ztgcHM_c9
#print axioms ztgcHM_c10
#print axioms ztgcHM_c11
#print axioms ztgcHM_c12
#print axioms ztgcHM_c13
#print axioms ztgcHM_c14
#print axioms ztgcHM_c15
#print axioms ztgcHM_c16
#print axioms ztgcHM_c17
#print axioms ztgcHM_c18
#print axioms ztgcHM_c19
#print axioms ztgcHM_c20
#print axioms ztgcHM_c21
#print axioms ztgcHM_c22
#print axioms ztgcHM_c23
#print axioms ztgcHM_c24
#print axioms ztgcHM_c25
#print axioms ztgcHM_c26
#print axioms ztgcHM_c27
#print axioms ztgcHM_c28
#print axioms ztgcHM_c29
#print axioms ztgcHM_c30

end Kepler.Text
