/-
Kepler.Text.ZTGTrioWide — lane `ztg-joint6-trio-w1`, M1/Stage A: the wide-box
ground layer of the W1 trio.  On the `1_0_0_0` bank box (critical slot `y3`,
`y3 ∈ [2·hminus, √8]`) the Cayley–Menger determinant stays positive:

* `ztgcTrio_f<i>` — the shared polynomial-in-`hminus` factor envelopes of the
  trio campaign (factored bodies over the five-digit envelope
  `hminus ∈ [1.23175, 1.23176]`, `nb17_hminus_bounds`);
* `ztgv<i>` — `deltaX ≥ cv > 0` at the 64 vertices of the box's x-space
  image (`x1 ∈ [(2hminus)², (2hplus)²]`, `x2/x4/x5/x6 ∈ [4, (2hminus)²]`,
  `x3 ∈ [(2hminus)², 8]`);
* `ztgTrio_concave_<i>` — `deltaX` is concave in each `xᵢ` (chord identity
  via the public `g4w_step` of `Gamma4Wide`), so the box minimum sits at a
  vertex;
* `ztgTrio1000_deltaY_pos` — the assembled `0 < deltaY` on `ztgBox 1 0 0 0`,
  the ground positivity fact consumed by every derivative certificate.

Machine-generated (`trio_gen_wide.py`); envelopes self-verified at three
`hminus` samples; every declaration axiom-audited; no `sorry`/`axiom`/
`native_decide`.
-/
import Kepler.Text.ZTGJointKit
import Kepler.Text.Gamma4Wide
import Kepler.Text.ZTGJoint0000Corners

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

/-! ## 1. Shared factor envelopes -/


theorem ztgcTrio_f0 : ((-708354684284159/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ∧ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ≤ ((-8443717014567343/3051757812500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f1 : ((-11432831/16000000 : ℝ)) ≤ hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ)) ∧ hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ)) ≤ ((-223286657/312500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f2 : ((40275329/16000000 : ℝ)) ≤ hminus ^ 2 + ((1/1 : ℝ)) ∧ hminus ^ 2 + ((1/1 : ℝ)) ≤ ((393317609/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f3 : ((27983329/16000000 : ℝ)) ≤ hminus ^ 2 + hminus + ((-1/1 : ℝ)) ∧ hminus ^ 2 + hminus + ((-1/1 : ℝ)) ≤ ((273280109/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f4 : ((4927/4000 : ℝ)) ≤ hminus ∧ hminus ≤ ((15397/12500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  constructor <;> linarith [hh.1, hh.2]

theorem ztgcTrio_f5 : ((-23724671/16000000 : ℝ)) ≤ hminus ^ 2 + ((-3/1 : ℝ)) ∧ hminus ^ 2 + ((-3/1 : ℝ)) ≤ ((-231682391/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f6 : ((16275329/8000000 : ℝ)) ≤ ((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ∧ ((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ≤ ((158942609/78125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f7 : ((56825987/16000000 : ℝ)) ≤ ((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ∧ ((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ≤ ((554952827/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f8 : ((-452354684284159/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ∧ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ≤ ((-5391959202067343/3051757812500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f9 : ((-443531543112959/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ∧ hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ≤ ((-84590872379561863/48828125000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f10 : ((-481040543691125123864423/102400000000000000000000 : ℝ)) ≤ hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ)) ∧ hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ)) ≤ ((-2293563842581764126627981913/488281250000000000000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  have hp5 : ((2903439703632953407/1024000000000000000 : ℝ)) ≤ hminus ^ 5 ∧ hminus ^ 5 ≤ ((865327585895733036757/305175781250000000000 : ℝ)) := by
    constructor <;> nlinarith [hp4.1, hp4.2, hh.1, hh.2]
  have hp6 : ((14305247419799561436289/4096000000000000000000 : ℝ)) ≤ hminus ^ 6 ∧ hminus ^ 6 ≤ ((13323448840036601566947529/3814697265625000000000000 : ℝ)) := by
    constructor <;> nlinarith [hp3.1, hp3.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2, hp5.1, hp5.2, hp6.1, hp6.2]

theorem ztgcTrio_f11 : ((-973177825455359/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ)) ∧ hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ)) ≤ ((-185608072086593113/48828125000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f12 : ((12275329/4000000 : ℝ)) ≤ ((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ)) ∧ ((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ)) ≤ ((119880109/39062500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f13 : ((40825987/16000000 : ℝ)) ≤ ((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ)) ∧ ((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ)) ≤ ((398702827/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f14 : ((-11301091292245832439/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ)) ≤ ((-17656909518720649089/10000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f15 : ((-12931071/3200 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ)) ≤ ((-126276141/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f16 : ((29481729/3200 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ)) ≤ ((287911359/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f17 : ((455546193/8 : ℝ)) ≤ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ∧ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ≤ ((1423612647/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f18 : ((-514643283324159/10240000 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ)) ≤ ((-12268994331869061/244140625 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f19 : ((-461232446970007658059623/163840000 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ)) ≤ ((-2199120257481218179362356913/781250000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  have hp5 : ((2903439703632953407/1024000000000000000 : ℝ)) ≤ hminus ^ 5 ∧ hminus ^ 5 ≤ ((865327585895733036757/305175781250000000000 : ℝ)) := by
    constructor <;> nlinarith [hp4.1, hp4.2, hh.1, hh.2]
  have hp6 : ((14305247419799561436289/4096000000000000000000 : ℝ)) ≤ hminus ^ 6 ∧ hminus ^ 6 ≤ ((13323448840036601566947529/3814697265625000000000000 : ℝ)) := by
    constructor <;> nlinarith [hp3.1, hp3.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2, hp5.1, hp5.2, hp6.1, hp6.2]

theorem ztgcTrio_f20 : ((-4759925527211795085198471/2500000000 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2615070455397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2615070455397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ)) ≤ ((-30461745076284984998511/16000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f21 : ((-2230733283/400000 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((-6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((-6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ)) ≤ ((-2788321881/500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f22 : ((171981561/16000 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ)) ≤ ((671814813/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f23 : ((704209161/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((6082871/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((6082871/1 : ℝ)) ≤ ((1100342211/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f24 : ((961430144789559/16000000 : ℝ)) ≤ ((56082871/1 : ℝ)) * hminus ^ 2 + ((-25000000/1 : ℝ)) ∧ ((56082871/1 : ℝ)) * hminus ^ 2 + ((-25000000/1 : ℝ)) ≤ ((9389182133825439/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f25 : ((-14935551308808582903/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ)) ≤ ((-11667741409441894857/5000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f26 : ((-6377305364574283639/3200 : ℝ)) ≤ ((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ)) ∧ ((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ)) ≤ ((-9963647976108854089/5000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f27 : ((-593249339859323279/256 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ)) ≤ ((-1448294953112969279/625 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f28 : ((-17962291948808582903/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ)) ≤ ((-14032382534441894857/5000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f29 : ((-360065833626506556932561519/160000000000 : ℝ)) ≤ ((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ)) ∧ ((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ)) ≤ ((-562560415530371607510704231/250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f30 : ((-7165315797651443885198471/2500000000 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((1097928225000000/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((1097928225000000/1 : ℝ)) ≤ ((-45855869986807034998511/16000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f31 : ((-7558598269711795085198471/2500000000 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3865070455397359/1 : ℝ)) * hminus ^ 2 + ((1402071775000000/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3865070455397359/1 : ℝ)) * hminus ^ 2 + ((1402071775000000/1 : ℝ)) ≤ ((-48372757926284984998511/16000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f32 : ((-16396762722645832439/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2972928225000000/1 : ℝ)) * hminus ^ 2 + ((509929544602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2972928225000000/1 : ℝ)) * hminus ^ 2 + ((509929544602641/1 : ℝ)) ≤ ((-25618742159345649089/10000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f33 : ((331214709/4 : ℝ)) ≤ ((100000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ)) ∧ ((100000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ)) ≤ ((2070153519/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f34 : ((372658537/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-14639043/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-14639043/1 : ℝ)) ≤ ((582294361/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f35 : ((-29949287248591040361911/10240000 : ℝ)) ≤ ((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-4864641125000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ)) ∧ ((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-4864641125000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ)) ≤ ((-11423957686311983990374529/3906250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f36 : ((-101192515280597154660392092807/32000000000000 : ℝ)) ≤ ((1250000000000000/1 : ℝ)) * hminus ^ 6 + ((-3597928225000000/1 : ℝ)) * hminus ^ 4 + ((472928225000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ)) ∧ ((1250000000000000/1 : ℝ)) * hminus ^ 6 + ((-3597928225000000/1 : ℝ)) * hminus ^ 4 + ((472928225000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ)) ≤ ((-316177283466053441882476260353/100000000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  have hp5 : ((2903439703632953407/1024000000000000000 : ℝ)) ≤ hminus ^ 5 ∧ hminus ^ 5 ≤ ((865327585895733036757/305175781250000000000 : ℝ)) := by
    constructor <;> nlinarith [hp4.1, hp4.2, hh.1, hh.2]
  have hp6 : ((14305247419799561436289/4096000000000000000000 : ℝ)) ≤ hminus ^ 6 ∧ hminus ^ 6 ≤ ((13323448840036601566947529/3814697265625000000000000 : ℝ)) := by
    constructor <;> nlinarith [hp3.1, hp3.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2, hp5.1, hp5.2, hp6.1, hp6.2]

theorem ztgcTrio_f37 : ((-646471710666201817831271/163840000 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2500000000000000/1 : ℝ)) * hminus ^ 4 + ((-793784675000000/1 : ℝ)) * hminus ^ 2 + ((830785994602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2500000000000000/1 : ℝ)) * hminus ^ 4 + ((-793784675000000/1 : ℝ)) * hminus ^ 2 + ((830785994602641/1 : ℝ)) ≤ ((-1541186491614146153279811269/390625000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  have hp5 : ((2903439703632953407/1024000000000000000 : ℝ)) ≤ hminus ^ 5 ∧ hminus ^ 5 ≤ ((865327585895733036757/305175781250000000000 : ℝ)) := by
    constructor <;> nlinarith [hp4.1, hp4.2, hh.1, hh.2]
  have hp6 : ((14305247419799561436289/4096000000000000000000 : ℝ)) ≤ hminus ^ 6 ∧ hminus ^ 6 ≤ ((13323448840036601566947529/3814697265625000000000000 : ℝ)) := by
    constructor <;> nlinarith [hp3.1, hp3.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2, hp5.1, hp5.2, hp6.1, hp6.2]

theorem ztgcTrio_f38 : ((-3876117413625962940841423/1250000000 : ℝ)) ≤ ((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-5587998680397359/1 : ℝ)) * hminus ^ 2 + ((2500000000000000/1 : ℝ)) ∧ ((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-5587998680397359/1 : ℝ)) * hminus ^ 2 + ((2500000000000000/1 : ℝ)) ≤ ((-49610605244880279540911/16000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrio_f39 : ((62789457228733790456111/16000000 : ℝ)) ≤ ((4033855130397359/1 : ℝ)) * hminus ^ 2 + ((-2195856450000000/1 : ℝ)) ∧ ((4033855130397359/1 : ℝ)) * hminus ^ 2 + ((-2195856450000000/1 : ℝ)) ≤ ((613193820503185118044631/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrio_f40 : ((-261197693214591364963228525703/64000000000000 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2195856450000000/1 : ℝ)) * hminus ^ 4 + ((-1821285780397359/1 : ℝ)) * hminus ^ 2 + ((1554143550000000/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2195856450000000/1 : ℝ)) * hminus ^ 4 + ((-1821285780397359/1 : ℝ)) * hminus ^ 2 + ((1554143550000000/1 : ℝ)) ≤ ((-204044930555872937854625608057/50000000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  have hp5 : ((2903439703632953407/1024000000000000000 : ℝ)) ≤ hminus ^ 5 ∧ hminus ^ 5 ≤ ((865327585895733036757/305175781250000000000 : ℝ)) := by
    constructor <;> nlinarith [hp4.1, hp4.2, hh.1, hh.2]
  have hp6 : ((14305247419799561436289/4096000000000000000000 : ℝ)) ≤ hminus ^ 6 ∧ hminus ^ 6 ≤ ((13323448840036601566947529/3814697265625000000000000 : ℝ)) := by
    constructor <;> nlinarith [hp3.1, hp3.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2, hp5.1, hp5.2, hp6.1, hp6.2]

theorem ztgcTrio_f41 : ((-22100153529608582903/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-4695856450000000/1 : ℝ)) * hminus ^ 2 + ((2232857769602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-4695856450000000/1 : ℝ)) * hminus ^ 2 + ((2232857769602641/1 : ℝ)) ≤ ((-17264932925066894857/5000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

/-! ## 2. The 64 box vertices -/

theorem ztgv0 : (177 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (177 : ℝ) ≤ ((16887434029134686/95367431640625 : ℝ))) hp1.1

theorem ztgv1 : (201 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
      have hf := ztgcTrio_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
      have hf := ztgcTrio_f2
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
      have hf := ztgcTrio_f3
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (201 : ℝ) ≤ ((251652498653295719514337/1250000000000000000000 : ℝ))) hp3.1

theorem ztgv2 : (218 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-3650129975773/30517578125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/1000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-56201051236976881/381469726562500 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/4000000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((136528486434344232134231/625000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((1333351450451419536331151/6103515625000000000000 : ℝ)) := by
      have hf := ztgcTrio_f5
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact le_trans (by norm_num : (218 : ℝ) ≤ ((136528486434344232134231/625000000000000000000 : ℝ))) hp5.1

theorem ztgv3 : (268 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (268 : ℝ) ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hp3.1

theorem ztgv4 : (201 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((446573314/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((11432831/250000 : ℝ)) := by
      have hf := ztgcTrio_f1
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((8992943571985153/78125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((4496733753021079/39062500000000 : ℝ)) := by
      have hf := ztgcTrio_f2
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((251652498653295719514337/1250000000000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((1228867890169579548417611/6103515625000000000000 : ℝ)) := by
      have hf := ztgcTrio_f3
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (201 : ℝ) ≤ ((251652498653295719514337/1250000000000000000000 : ℝ))) hp3.1

theorem ztgv5 : (260 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by norm_num
    have hp1 : ((16275329/62500 : ℝ)) ≤ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2543081744/9765625 : ℝ)) := by
      have hf := ztgcTrio_f6
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (260 : ℝ) ≤ ((16275329/62500 : ℝ))) hp1.1

theorem ztgv6 : (268 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (268 : ℝ) ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hp3.1

theorem ztgv7 : (344 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by norm_num
    have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
      have hf := ztgcTrio_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (344 : ℝ) ≤ ((1379469530174723/4000000000000 : ℝ))) hp3.1

theorem ztgv8 : (177 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (177 : ℝ) ≤ ((16887434029134686/95367431640625 : ℝ))) hp1.1

theorem ztgv9 : (177 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((16887434029134686/95367431640625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((708354684284159/4000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (177 : ℝ) ≤ ((16887434029134686/95367431640625 : ℝ))) hp1.1

theorem ztgv10 : (226 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-128/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) ∧ ((-128/1 : ℝ)) ≤ ((-128/1 : ℝ)) := by norm_num
    have hp1 : ((21567836808269372/95367431640625 : ℝ)) ≤ ((-128/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((-128/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((452354684284159/2000000000000 : ℝ)) := by
      have hf := ztgcTrio_f8
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (226 : ℝ) ≤ ((21567836808269372/95367431640625 : ℝ))) hp1.1

theorem ztgv11 : (260 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by norm_num
    have hp1 : ((16275329/62500 : ℝ)) ≤ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2543081744/9765625 : ℝ)) := by
      have hf := ztgcTrio_f6
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (260 : ℝ) ≤ ((16275329/62500 : ℝ))) hp1.1

theorem ztgv12 : (225 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-1271540872/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((-16275329/125000 : ℝ)) := by
      have hf := ztgcTrio_f6
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((1376744278374382196177927/6103515625000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) * (hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((70496060636169685170031/312500000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f9
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact le_trans (by norm_num : (225 : ℝ) ≤ ((1376744278374382196177927/6103515625000000000000 : ℝ))) hp2.1

theorem ztgv13 : (268 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (268 : ℝ) ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hp3.1

theorem ztgv14 : (300 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((2293563842581764126627981913/7629394531250000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ))) ≤ ((481040543691125123864423/1600000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f10
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (300 : ℝ) ≤ ((2293563842581764126627981913/7629394531250000000000000 : ℝ))) hp1.1

theorem ztgv15 : (369 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((4505697014957764307209177/12207031250000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) ≤ ((230708940212521294366631/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f11
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (369 : ℝ) ≤ ((4505697014957764307209177/12207031250000000000000 : ℝ))) hp3.1

theorem ztgv16 : (227 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by norm_num
    have hp1 : ((56825987/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((2219811308/9765625 : ℝ)) := by
      have hf := ztgcTrio_f7
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (227 : ℝ) ≤ ((56825987/250000 : ℝ))) hp1.1

theorem ztgv17 : (268 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (268 : ℝ) ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hp3.1

theorem ztgv18 : (268 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (268 : ℝ) ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hp3.1

theorem ztgv19 : (344 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by norm_num
    have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
      have hf := ztgcTrio_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (344 : ℝ) ≤ ((1379469530174723/4000000000000 : ℝ))) hp3.1

theorem ztgv20 : (268 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (268 : ℝ) ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hp3.1

theorem ztgv21 : (344 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by norm_num
    have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
      have hf := ztgcTrio_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (344 : ℝ) ≤ ((1379469530174723/4000000000000 : ℝ))) hp3.1

theorem ztgv22 : (344 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) = ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) ∧ ((64/1 : ℝ)) ≤ ((64/1 : ℝ)) := by norm_num
    have hp1 : ((9854/125 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) ≤ ((246352/3125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/250000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) ≤ ((948270436/9765625 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1379469530174723/4000000000000 : ℝ)) ≤ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((64/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((131561339804680643/381469726562500 : ℝ)) := by
      have hf := ztgcTrio_f7
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (344 : ℝ) ≤ ((1379469530174723/4000000000000 : ℝ))) hp3.1

theorem ztgv23 : (447 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by norm_num
    have hp1 : ((19708/125 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) ≤ ((492704/3125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/125000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) ≤ ((1896540872/9765625 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/500000000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((7300259951546/30517578125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/2000000000000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/190734863281250 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((2903439703632953407/8000000000000000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((865327585895733036757/2384185791015625000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    have hp6 : ((14305247419799561436289/32000000000000000000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((13323448840036601566947529/29802322387695312500000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp5.1, hp5.2, hf.1, hf.2]
    exact le_trans (by norm_num : (447 : ℝ) ≤ ((14305247419799561436289/32000000000000000000 : ℝ))) hp6.1

theorem ztgv24 : (243 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((185608072086593113/762939453125000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) ≤ ((973177825455359/4000000000000 : ℝ)) := by
      have hf := ztgcTrio_f11
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (243 : ℝ) ≤ ((185608072086593113/762939453125000 : ℝ))) hp1.1

theorem ztgv25 : (268 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/762939453125000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (268 : ℝ) ≤ ((204974008511520043980847/762939453125000000000 : ℝ))) hp3.1

theorem ztgv26 : (300 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((2293563842581764126627981913/7629394531250000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ))) ≤ ((481040543691125123864423/1600000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f10
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (300 : ℝ) ≤ ((2293563842581764126627981913/7629394531250000000000000 : ℝ))) hp1.1

theorem ztgv27 : (369 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((4505697014957764307209177/12207031250000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) ≤ ((230708940212521294366631/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f11
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (369 : ℝ) ≤ ((4505697014957764307209177/12207031250000000000000 : ℝ))) hp3.1

theorem ztgv28 : (300 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((2293563842581764126627981913/7629394531250000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus ^ 6 + ((-2/1 : ℝ)) * hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((4/1 : ℝ))) ≤ ((481040543691125123864423/1600000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f10
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (300 : ℝ) ≤ ((2293563842581764126627981913/7629394531250000000000000 : ℝ))) hp1.1

theorem ztgv29 : (369 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) ∧ ((-64/1 : ℝ)) ≤ ((-64/1 : ℝ)) := by norm_num
    have hp1 : ((-246352/3125 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) ≤ ((-9854/125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/9765625 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/250000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((4505697014957764307209177/12207031250000000000000 : ℝ)) ≤ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) ∧ ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-6/1 : ℝ)) * hminus ^ 2 + ((3/1 : ℝ))) ≤ ((230708940212521294366631/625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f11
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (369 : ℝ) ≤ ((4505697014957764307209177/12207031250000000000000 : ℝ))) hp3.1

theorem ztgv30 : (392 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) = ((128/1 : ℝ)) * (((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by norm_num
    have hp1 : ((12275329/31250 : ℝ)) ≤ ((128/1 : ℝ)) * (((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((128/1 : ℝ)) * (((4/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((3836163488/9765625 : ℝ)) := by
      have hf := ztgcTrio_f12
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (392 : ℝ) ≤ ((12275329/31250 : ℝ))) hp1.1

theorem ztgv31 : (495 : ℝ) ≤ deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((128/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) := by
      unfold deltaX; ring
    rw [hE]
    have hp0 : ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) ∧ ((128/1 : ℝ)) ≤ ((128/1 : ℝ)) := by norm_num
    have hp1 : ((19708/125 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) ≤ ((492704/3125 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/125000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) ≤ ((1896540872/9765625 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((991064266174723/2000000000000 : ℝ)) ≤ ((128/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((128/1 : ℝ)) * (hminus) * (hminus) * (((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((94519525898430643/190734863281250 : ℝ)) := by
      have hf := ztgcTrio_f13
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (495 : ℝ) ≤ ((991064266174723/2000000000000 : ℝ))) hp3.1

theorem ztgv32 : (180 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((17656909518720649089/97656250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ≤ ((11301091292245832439/62500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f14
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (180 : ℝ) ≤ ((17656909518720649089/97656250000000000 : ℝ))) hp1.1

theorem ztgv33 : (217 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((126276141/305175781250000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) ≤ ((12931071/31250000000000000 : ℝ)) := by
      have hf := ztgcTrio_f15
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((3722838968127789/976562500000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) ≤ ((3723002224935489/976562500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f16
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1695925119082662616457277/7812500000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ≤ ((5300113052227300899529383/24414062500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f17
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (217 : ℝ) ≤ ((1695925119082662616457277/7812500000000000000000 : ℝ))) hp3.1

theorem ztgv34 : (225 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-43917129/9765625000000 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-43917129/9765625000000 : ℝ)) ≤ ((-43917129/9765625000000 : ℝ)) ∧ ((-43917129/9765625000000 : ℝ)) ≤ ((-43917129/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((538819006772962363045869/2384185791015625000000 : ℝ)) ≤ ((-43917129/9765625000000 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ∧ ((-43917129/9765625000000 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ≤ ((22601655462730639619511/100000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f18
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (225 : ℝ) ≤ ((538819006772962363045869/2384185791015625000000 : ℝ))) hp1.1

theorem ztgv35 : (288 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((2199120257481218179362356913/7629394531250000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((461232446970007658059623/1600000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f19
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (288 : ℝ) ≤ ((2199120257481218179362356913/7629394531250000000000000 : ℝ))) hp1.1

theorem ztgv36 : (194 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2615070455397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((30461745076284984998511/156250000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2615070455397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2615070455397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ))) ≤ ((4759925527211795085198471/24414062500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f20
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (194 : ℝ) ≤ ((30461745076284984998511/156250000000000000000 : ℝ))) hp1.1

theorem ztgv37 : (270 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((6082871/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((2788321881/4882812500000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) ≤ ((2230733283/3906250000000000000 : ℝ)) := by
      have hf := ztgcTrio_f21
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((479539949664836241/78125000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) ≤ ((1498639663371521079/244140625000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f22
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((337696425619456560477003801/1250000000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((6082871/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((6627/1 : ℝ)) * hminus + ((-5000/1 : ℝ))) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((6082871/1 : ℝ))) ≤ ((1649016480686515218499965669/6103515625000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f23
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (270 : ℝ) ≤ ((337696425619456560477003801/1250000000000000000000000 : ℝ))) hp3.1

theorem ztgv38 : (270 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) = ((43917129/9765625000000 : ℝ)) * (((56082871/1 : ℝ)) * hminus ^ 2 + ((-25000000/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((43917129/9765625000000 : ℝ)) ≤ ((43917129/9765625000000 : ℝ)) ∧ ((43917129/9765625000000 : ℝ)) ≤ ((43917129/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((42223251693211740456111/156250000000000000000 : ℝ)) ≤ ((43917129/9765625000000 : ℝ)) * (((56082871/1 : ℝ)) * hminus ^ 2 + ((-25000000/1 : ℝ))) ∧ ((43917129/9765625000000 : ℝ)) * (((56082871/1 : ℝ)) * hminus ^ 2 + ((-25000000/1 : ℝ))) ≤ ((412345922975707068044631/1525878906250000000000 : ℝ)) := by
      have hf := ztgcTrio_f24
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (270 : ℝ) ≤ ((42223251693211740456111/156250000000000000000 : ℝ))) hp1.1

theorem ztgv39 : (362 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((-15397/122070312500000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) ≤ ((-4927/39062500000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/1525878906250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/156250000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((283238261401125704037082953/781250000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) ≤ ((3540735437876071387492488927/9765625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f25
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (362 : ℝ) ≤ ((283238261401125704037082953/781250000000000000000000 : ℝ))) hp3.1

theorem ztgv40 : (188 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * 2) = ((1837998680397359/9765625000000 : ℝ)) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((1837998680397359/9765625000000 : ℝ)) ≤ ((1837998680397359/9765625000000 : ℝ)) ∧ ((1837998680397359/9765625000000 : ℝ)) ≤ ((1837998680397359/9765625000000 : ℝ)) := by norm_num
    exact le_trans (by norm_num) hp0.1

theorem ztgv41 : (204 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((9963647976108854089/48828125000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ≤ ((6377305364574283639/31250000000000000 : ℝ)) := by
      have hf := ztgcTrio_f26
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (204 : ℝ) ≤ ((9963647976108854089/48828125000000000 : ℝ))) hp1.1

theorem ztgv42 : (237 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((1448294953112969279/6103515625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ≤ ((593249339859323279/2500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f27
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (237 : ℝ) ≤ ((1448294953112969279/6103515625000000 : ℝ))) hp1.1

theorem ztgv43 : (287 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((14032382534441894857/48828125000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ≤ ((17962291948808582903/62500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f28
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (287 : ℝ) ≤ ((14032382534441894857/48828125000000000 : ℝ))) hp1.1

theorem ztgv44 : (230 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((562560415530371607510704231/2441406250000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((625000000000000/1 : ℝ))) ≤ ((360065833626506556932561519/1562500000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f29
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (230 : ℝ) ≤ ((562560415530371607510704231/2441406250000000000000000 : ℝ))) hp1.1

theorem ztgv45 : (293 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((1097928225000000/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((45855869986807034998511/156250000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((1097928225000000/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3560926905397359/1 : ℝ)) * hminus ^ 2 + ((1097928225000000/1 : ℝ))) ≤ ((7165315797651443885198471/24414062500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f30
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (293 : ℝ) ≤ ((45855869986807034998511/156250000000000000000 : ℝ))) hp1.1

theorem ztgv46 : (309 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3865070455397359/1 : ℝ)) * hminus ^ 2 + ((1402071775000000/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((48372757926284984998511/156250000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3865070455397359/1 : ℝ)) * hminus ^ 2 + ((1402071775000000/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3865070455397359/1 : ℝ)) * hminus ^ 2 + ((1402071775000000/1 : ℝ))) ≤ ((7558598269711795085198471/24414062500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f31
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (309 : ℝ) ≤ ((48372757926284984998511/156250000000000000000 : ℝ))) hp1.1

theorem ztgv47 : (398 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2972928225000000/1 : ℝ)) * hminus ^ 2 + ((509929544602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((-15397/122070312500000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) ≤ ((-4927/39062500000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/1525878906250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/156250000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((621903394484286056354025281/1562500000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2972928225000000/1 : ℝ)) * hminus ^ 2 + ((509929544602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2972928225000000/1 : ℝ)) * hminus ^ 2 + ((509929544602641/1 : ℝ))) ≤ ((3887141333997977650128368351/9765625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f32
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (398 : ℝ) ≤ ((621903394484286056354025281/1562500000000000000000000 : ℝ))) hp3.1

theorem ztgv48 : (238 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((11667741409441894857/48828125000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) ≤ ((14935551308808582903/62500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f25
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (238 : ℝ) ≤ ((11667741409441894857/48828125000000000 : ℝ))) hp1.1

theorem ztgv49 : (288 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((2199120257481218179362356913/7629394531250000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((461232446970007658059623/1600000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f19
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (288 : ℝ) ≤ ((2199120257481218179362356913/7629394531250000000000000 : ℝ))) hp1.1

theorem ztgv50 : (288 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((2199120257481218179362356913/7629394531250000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((461232446970007658059623/1600000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f19
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (288 : ℝ) ≤ ((2199120257481218179362356913/7629394531250000000000000 : ℝ))) hp1.1

theorem ztgv51 : (372 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((43917129/9765625000000 : ℝ)) * (((100000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((43917129/9765625000000 : ℝ)) ≤ ((43917129/9765625000000 : ℝ)) ∧ ((43917129/9765625000000 : ℝ)) ≤ ((43917129/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((14545999101850461/39062500000000 : ℝ)) ≤ ((43917129/9765625000000 : ℝ)) * (((100000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ))) ∧ ((43917129/9765625000000 : ℝ)) * (((100000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ))) ≤ ((90915199143726951/244140625000000 : ℝ)) := by
      have hf := ztgcTrio_f33
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (372 : ℝ) ≤ ((14545999101850461/39062500000000 : ℝ))) hp1.1

theorem ztgv52 : (274 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((-15397/122070312500000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) ≤ ((-4927/39062500000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/1525878906250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/156250000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((428627287690175415729025281/1562500000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ≤ ((2679122691743439736528368351/9765625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f14
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (274 : ℝ) ≤ ((428627287690175415729025281/1562500000000000000000000 : ℝ))) hp3.1

theorem ztgv53 : (362 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((-15397/122070312500000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) ≤ ((-4927/39062500000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/1525878906250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/156250000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((283238261401125704037082953/781250000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) ≤ ((3540735437876071387492488927/9765625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f25
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (362 : ℝ) ≤ ((283238261401125704037082953/781250000000000000000000 : ℝ))) hp3.1

theorem ztgv54 : (362 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) = ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((-15397/122070312500000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) ≤ ((-4927/39062500000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/1525878906250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/156250000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((283238261401125704037082953/781250000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((1455785994602641/1 : ℝ))) ≤ ((3540735437876071387492488927/9765625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f25
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (362 : ℝ) ≤ ((283238261401125704037082953/781250000000000000000000 : ℝ))) hp3.1

theorem ztgv55 : (476 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((131751387/9765625000000 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-14639043/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((131751387/9765625000000 : ℝ)) ≤ ((131751387/9765625000000 : ℝ)) ∧ ((131751387/9765625000000 : ℝ)) ≤ ((131751387/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((649139083749/39062500000000000 : ℝ)) ≤ ((131751387/9765625000000 : ℝ)) * (hminus) ∧ ((131751387/9765625000000 : ℝ)) * (hminus) ≤ ((2028576105639/122070312500000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((3198308265631323/156250000000000000000 : ℝ)) ≤ ((131751387/9765625000000 : ℝ)) * (hminus) * (hminus) ∧ ((131751387/9765625000000 : ℝ)) * (hminus) * (hminus) ≤ ((31233986298523683/1525878906250000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1191876879145176210554451/2500000000000000000000 : ℝ)) ≤ ((131751387/9765625000000 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-14639043/1 : ℝ))) ∧ ((131751387/9765625000000 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-14639043/1 : ℝ))) ≤ ((18187374093181603235851563/38146972656250000000000 : ℝ)) := by
      have hf := ztgcTrio_f34
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (476 : ℝ) ≤ ((1191876879145176210554451/2500000000000000000000 : ℝ))) hp3.1

theorem ztgv56 : (262 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2972928225000000/1 : ℝ)) * hminus ^ 2 + ((509929544602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((25618742159345649089/97656250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2972928225000000/1 : ℝ)) * hminus ^ 2 + ((509929544602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2972928225000000/1 : ℝ)) * hminus ^ 2 + ((509929544602641/1 : ℝ))) ≤ ((16396762722645832439/62500000000000000 : ℝ)) := by
      have hf := ztgcTrio_f32
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (262 : ℝ) ≤ ((25618742159345649089/97656250000000000 : ℝ))) hp1.1

theorem ztgv57 : (299 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-4864641125000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((11423957686311983990374529/38146972656250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-4864641125000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((1097928225000000/1 : ℝ)) * hminus ^ 4 + ((-4864641125000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((29949287248591040361911/100000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f35
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (299 : ℝ) ≤ ((11423957686311983990374529/38146972656250000000000 : ℝ))) hp1.1

theorem ztgv58 : (323 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 6 + ((-3597928225000000/1 : ℝ)) * hminus ^ 4 + ((472928225000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((316177283466053441882476260353/976562500000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 6 + ((-3597928225000000/1 : ℝ)) * hminus ^ 4 + ((472928225000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 6 + ((-3597928225000000/1 : ℝ)) * hminus ^ 4 + ((472928225000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ≤ ((101192515280597154660392092807/312500000000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f36
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (323 : ℝ) ≤ ((316177283466053441882476260353/976562500000000000000000000 : ℝ))) hp1.1

theorem ztgv59 : (404 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2500000000000000/1 : ℝ)) * hminus ^ 4 + ((-793784675000000/1 : ℝ)) * hminus ^ 2 + ((830785994602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((1541186491614146153279811269/3814697265625000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2500000000000000/1 : ℝ)) * hminus ^ 4 + ((-793784675000000/1 : ℝ)) * hminus ^ 2 + ((830785994602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2500000000000000/1 : ℝ)) * hminus ^ 4 + ((-793784675000000/1 : ℝ)) * hminus ^ 2 + ((830785994602641/1 : ℝ))) ≤ ((646471710666201817831271/1600000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f37
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (404 : ℝ) ≤ ((1541186491614146153279811269/3814697265625000000000000 : ℝ))) hp1.1

theorem ztgv60 : (317 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-5587998680397359/1 : ℝ)) * hminus ^ 2 + ((2500000000000000/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((49610605244880279540911/156250000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-5587998680397359/1 : ℝ)) * hminus ^ 2 + ((2500000000000000/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-5587998680397359/1 : ℝ)) * hminus ^ 2 + ((2500000000000000/1 : ℝ))) ≤ ((3876117413625962940841423/12207031250000000000000 : ℝ)) := by
      have hf := ztgcTrio_f38
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (317 : ℝ) ≤ ((49610605244880279540911/156250000000000000000 : ℝ))) hp1.1

theorem ztgv61 : (401 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((1/9765625000000 : ℝ)) * (((4033855130397359/1 : ℝ)) * hminus ^ 2 + ((-2195856450000000/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((1/9765625000000 : ℝ)) ≤ ((1/9765625000000 : ℝ)) ∧ ((1/9765625000000 : ℝ)) ≤ ((1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((62789457228733790456111/156250000000000000000 : ℝ)) ≤ ((1/9765625000000 : ℝ)) * (((4033855130397359/1 : ℝ)) * hminus ^ 2 + ((-2195856450000000/1 : ℝ))) ∧ ((1/9765625000000 : ℝ)) * (((4033855130397359/1 : ℝ)) * hminus ^ 2 + ((-2195856450000000/1 : ℝ))) ≤ ((613193820503185118044631/1525878906250000000000 : ℝ)) := by
      have hf := ztgcTrio_f39
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (401 : ℝ) ≤ ((62789457228733790456111/156250000000000000000 : ℝ))) hp1.1

theorem ztgv62 : (417 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2195856450000000/1 : ℝ)) * hminus ^ 4 + ((-1821285780397359/1 : ℝ)) * hminus ^ 2 + ((1554143550000000/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((204044930555872937854625608057/488281250000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2195856450000000/1 : ℝ)) * hminus ^ 4 + ((-1821285780397359/1 : ℝ)) * hminus ^ 2 + ((1554143550000000/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-2195856450000000/1 : ℝ)) * hminus ^ 4 + ((-1821285780397359/1 : ℝ)) * hminus ^ 2 + ((1554143550000000/1 : ℝ))) ≤ ((261197693214591364963228525703/625000000000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f40
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact le_trans (by norm_num : (417 : ℝ) ≤ ((204044930555872937854625608057/488281250000000000000000000 : ℝ))) hp1.1

theorem ztgv63 : (536 : ℝ) ≤ deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) :=
  by
    have hhp : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
      rw [hplus]; norm_num
    have hE : deltaX (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-4695856450000000/1 : ℝ)) * hminus ^ 2 + ((2232857769602641/1 : ℝ))) := by
      unfold deltaX; rw [hhp]; ring
    rw [hE]
    have hp0 : ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) ∧ ((-1/9765625000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) := by norm_num
    have hp1 : ((-15397/122070312500000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) ≤ ((-4927/39062500000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/1525878906250000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/156250000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f4
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((419111926918931219662082953/781250000000000000000000 : ℝ)) ≤ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-4695856450000000/1 : ℝ)) * hminus ^ 2 + ((2232857769602641/1 : ℝ))) ∧ ((-1/9765625000000 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-4695856450000000/1 : ℝ)) * hminus ^ 2 + ((2232857769602641/1 : ℝ))) ≤ ((5239230555797217454692488927/9765625000000000000000000 : ℝ)) := by
      have hf := ztgcTrio_f41
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact le_trans (by norm_num : (536 : ℝ) ≤ ((419111926918931219662082953/781250000000000000000000 : ℝ))) hp3.1

/-! ## 3. Per-slot concavity of `deltaX` -/

theorem ztgTrio_concave_1 (x2 x3 x4 x5 x6 : ℝ) (hxopp : 0 ≤ x4)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6) ≤ deltaX t x2 x3 x4 x5 x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX t x2 x3 x4 x5 x6 - (lam * deltaX a x2 x3 x4 x5 x6 + (1 - lam) * deltaX b x2 x3 x4 x5 x6)
      = x4 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX s x2 x3 x4 x5 x6) hat htb hab
    hxopp hkey

theorem ztgTrio_concave_2 (x1 x3 x4 x5 x6 : ℝ) (hxopp : 0 ≤ x5)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6) ≤ deltaX x1 t x3 x4 x5 x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 t x3 x4 x5 x6 - (lam * deltaX x1 a x3 x4 x5 x6 + (1 - lam) * deltaX x1 b x3 x4 x5 x6)
      = x5 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 s x3 x4 x5 x6) hat htb hab
    hxopp hkey

theorem ztgTrio_concave_3 (x1 x2 x4 x5 x6 : ℝ) (hxopp : 0 ≤ x6)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6) ≤ deltaX x1 x2 t x4 x5 x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 x2 t x4 x5 x6 - (lam * deltaX x1 x2 a x4 x5 x6 + (1 - lam) * deltaX x1 x2 b x4 x5 x6)
      = x6 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 x2 s x4 x5 x6) hat htb hab
    hxopp hkey

theorem ztgTrio_concave_4 (x1 x2 x3 x5 x6 : ℝ) (hxopp : 0 ≤ x1)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6) ≤ deltaX x1 x2 x3 t x5 x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 x2 x3 t x5 x6 - (lam * deltaX x1 x2 x3 a x5 x6 + (1 - lam) * deltaX x1 x2 x3 b x5 x6)
      = x1 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 x2 x3 s x5 x6) hat htb hab
    hxopp hkey

theorem ztgTrio_concave_5 (x1 x2 x3 x4 x6 : ℝ) (hxopp : 0 ≤ x2)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6) ≤ deltaX x1 x2 x3 x4 t x6 := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 x2 x3 x4 t x6 - (lam * deltaX x1 x2 x3 x4 a x6 + (1 - lam) * deltaX x1 x2 x3 x4 b x6)
      = x2 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 x2 x3 x4 s x6) hat htb hab
    hxopp hkey

theorem ztgTrio_concave_6 (x1 x2 x3 x4 x5 : ℝ) (hxopp : 0 ≤ x3)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b) ≤ deltaX x1 x2 x3 x4 x5 t := by
  have hba : b - a ≠ 0 := by linarith
  set lam := (b - t) / (b - a) with hlam
  have hkey : deltaX x1 x2 x3 x4 x5 t - (lam * deltaX x1 x2 x3 x4 x5 a + (1 - lam) * deltaX x1 x2 x3 x4 x5 b)
      = x3 * ((t - a) * (b - t)) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  exact g4w_step (f := fun s => deltaX x1 x2 x3 x4 x5 s) hat htb hab
    hxopp hkey

/-! ## 4. The assembled `deltaY > 0` on the `1_0_0_0` box -/

/-- Two-phase corner walk: for `x3 = y3² ≤ 7.02674064` the point is inside
the `Gamma4Wide` box (`96 ≤ deltaX`); on the sliver `x3 ∈ [7.02674064, 8]`
one `ztgTrio_concave_3` step reduces to the two `x3` endpoints, of which the
`7.02674064` endpoint is again `g4w`-covered and the `x3 = 8` endpoint falls
to a five-level walk over `x1, x2, x4, x5, x6` ending at the 32 `x3 = 8`
vertices `ztgv<i>` (each `≥ 177 ≥ 96`). -/
theorem ztgTrio1000_deltaY_pos {y1 y2 y3 y4 y5 y6 : ℝ}
    (hy : ztgBox 1 0 0 0 y1 y2 y3 y4 y5 y6) :
    (0:ℝ) < deltaY y1 y2 y3 y4 y5 y6 := by
  rcases hy with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have h8sq : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hp0 : (0:ℝ) ≤ 2 * hplus := by rw [hplus]; norm_num
  have hhm : (0:ℝ) ≤ 2 * hminus := by linarith
  have h2l' : (2:ℝ) ≤ y2 := by simpa [bank_ZTGIJCF4lo] using h2l
  have h2h' : y2 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h2h
  have h3l' : 2 * hminus ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3h' : y3 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h3h
  have h4l' : (2:ℝ) ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4h' : y4 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h4h
  have h5l' : (2:ℝ) ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5h' : y5 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h5h
  have h6l' : (2:ℝ) ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6h' : y6 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h6h
  have hp1 : (0:ℝ) ≤ y1 := by linarith
  have hp2 : (0:ℝ) ≤ y2 := by linarith
  have hp3 : (0:ℝ) ≤ y3 := by linarith
  have hp4 : (0:ℝ) ≤ y4 := by linarith
  have hp5 : (0:ℝ) ≤ y5 := by linarith
  have hp6 : (0:ℝ) ≤ y6 := by linarith
  have hs1l : (2 * hminus * (2 * hminus)) ≤ y1 * y1 := by nlinarith [hhm, hp1, h1l]
  have hs1u : y1 * y1 ≤ (2 * hplus * (2 * hplus)) := by nlinarith [hp1, h1h]
  have hs2l : (2 * 2) ≤ y2 * y2 := by nlinarith [h2l']
  have hs2u : y2 * y2 ≤ (2 * hminus * (2 * hminus)) := by nlinarith [hp2, h2h']
  have hs3l : (2 * hminus * (2 * hminus)) ≤ y3 * y3 := by nlinarith [hhm, hp3, h3l']
  have hs3u : y3 * y3 ≤ 8 := by nlinarith [hp3, h3h', h8sq]
  have hs4l : (2 * 2) ≤ y4 * y4 := by nlinarith [h4l']
  have hs4u : y4 * y4 ≤ (2 * hminus * (2 * hminus)) := by nlinarith [hp4, h4h']
  have hs5l : (2 * 2) ≤ y5 * y5 := by nlinarith [h5l']
  have hs5u : y5 * y5 ≤ (2 * hminus * (2 * hminus)) := by nlinarith [hp5, h5h']
  have hs6l : (2 * 2) ≤ y6 * y6 := by nlinarith [h6l']
  have hs6u : y6 * y6 ≤ (2 * hminus * (2 * hminus)) := by nlinarith [hp6, h6h']
  have hhp02 : (0:ℝ) ≤ 2 * hplus * (2 * hplus) := by nlinarith [hp0]
  have hhm2 : (0:ℝ) ≤ 2 * hminus * (2 * hminus) := by nlinarith [hhm, hhm]
  have hhpv : (2 * hplus * (2 * hplus)) = 7.02674064 := by rw [hplus]; norm_num
  by_cases hy3 : y3 * y3 ≤ 7.02674064
  · have hpack : g4wBox (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
      refine ⟨by nlinarith, ?_, by nlinarith, ?_, by nlinarith, hy3, by nlinarith, ?_,
        by nlinarith, ?_, by nlinarith, ?_⟩
      · nlinarith [hs1u, hhpv]
      · nlinarith [hs2u, hhpv]
      · nlinarith [hs4u, hhpv]
      · nlinarith [hs5u, hhpv]
      · nlinarith [hs6u, hhpv]
    have hd := g4w_deltaX_bounds hpack
    unfold deltaY
    linarith
  · have h3ge : 7.02674064 ≤ y3 * y3 := le_of_not_ge hy3
    have h6p : (0:ℝ) ≤ y6 * y6 := by nlinarith
    have h38 : (7.02674064:ℝ) < 8 := by norm_num
    have hab1 : (2 * hminus * (2 * hminus)) < (2 * hplus * (2 * hplus)) := by
      nlinarith [hh.1, hh.2, hp0]
    have hab2 : (2 * 2) < (2 * hminus * (2 * hminus)) := by nlinarith [hh.1, hh.2]
    have hfix : g4wBox (y1*y1) (y2*y2) 7.02674064 (y4*y4) (y5*y5) (y6*y6) := by
      exact ⟨by nlinarith, by nlinarith [hs1u, hhpv], by nlinarith,
        by nlinarith [hs2u, hhpv], by norm_num, by norm_num, by nlinarith,
        by nlinarith [hs4u, hhpv], by nlinarith, by nlinarith [hs5u, hhpv],
        by nlinarith, by nlinarith [hs6u, hhpv]⟩
    have b1 : (96:ℝ) ≤ deltaX (y1*y1) (y2*y2) 7.02674064 (y4*y4) (y5*y5) (y6*y6) :=
      g4w_deltaX_bounds hfix
    have b2 : (96:ℝ) ≤ min (deltaX (y1*y1) (y2*y2) 7.02674064 (y4*y4) (y5*y5) (y6*y6))
        (deltaX (y1*y1) (y2*y2) 8 (y4*y4) (y5*y5) (y6*y6)) := by
      refine le_min b1 ?_
      refine le_trans ?_ (ztgTrio_concave_1 _ _ _ _ _ (by nlinarith [h4l']) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) _ hs1l hs1u hab1)
      refine le_min ?_ ?_
      all_goals
        refine le_trans ?_ (ztgTrio_concave_2 _ _ _ _ _ (by nlinarith [h5l']) (2 * 2) (2 * hminus * (2 * hminus)) _ hs2l hs2u hab2)
        refine le_min ?_ ?_
      · refine le_trans ?_ (ztgTrio_concave_4 _ _ _ _ _ hhm2 (2 * 2) (2 * hminus * (2 * hminus)) _ hs4l hs4u hab2)
        refine le_min ?_ ?_
        all_goals
          refine le_trans ?_ (ztgTrio_concave_5 _ _ _ _ _ (by norm_num) (2 * 2) (2 * hminus * (2 * hminus)) _ hs5l hs5u hab2)
          refine le_min ?_ ?_
        all_goals
          refine le_trans ?_ (ztgTrio_concave_6 _ _ _ _ _ (by norm_num) (2 * 2) (2 * hminus * (2 * hminus)) _ hs6l hs6u hab2)
          refine le_min ?_ ?_
          all_goals first
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (177 : ℝ)) ztgv8)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (177 : ℝ)) ztgv9)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (226 : ℝ)) ztgv10)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (260 : ℝ)) ztgv11)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (225 : ℝ)) ztgv12)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (268 : ℝ)) ztgv13)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (300 : ℝ)) ztgv14)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (369 : ℝ)) ztgv15)
      · refine le_trans ?_ (ztgTrio_concave_4 _ _ _ _ _ hhm2 (2 * 2) (2 * hminus * (2 * hminus)) _ hs4l hs4u hab2)
        refine le_min ?_ ?_
        all_goals
          refine le_trans ?_ (ztgTrio_concave_5 _ _ _ _ _ hhm2 (2 * 2) (2 * hminus * (2 * hminus)) _ hs5l hs5u hab2)
          refine le_min ?_ ?_
        all_goals
          refine le_trans ?_ (ztgTrio_concave_6 _ _ _ _ _ (by norm_num) (2 * 2) (2 * hminus * (2 * hminus)) _ hs6l hs6u hab2)
          refine le_min ?_ ?_
          all_goals first
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (243 : ℝ)) ztgv24)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (268 : ℝ)) ztgv25)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (300 : ℝ)) ztgv26)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (369 : ℝ)) ztgv27)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (300 : ℝ)) ztgv28)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (369 : ℝ)) ztgv29)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (392 : ℝ)) ztgv30)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (495 : ℝ)) ztgv31)
      · refine le_trans ?_ (ztgTrio_concave_4 _ _ _ _ _ hhp02 (2 * 2) (2 * hminus * (2 * hminus)) _ hs4l hs4u hab2)
        refine le_min ?_ ?_
        all_goals
          refine le_trans ?_ (ztgTrio_concave_5 _ _ _ _ _ (by norm_num) (2 * 2) (2 * hminus * (2 * hminus)) _ hs5l hs5u hab2)
          refine le_min ?_ ?_
        all_goals
          refine le_trans ?_ (ztgTrio_concave_6 _ _ _ _ _ (by norm_num) (2 * 2) (2 * hminus * (2 * hminus)) _ hs6l hs6u hab2)
          refine le_min ?_ ?_
          all_goals first
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (188 : ℝ)) ztgv40)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (204 : ℝ)) ztgv41)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (237 : ℝ)) ztgv42)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (287 : ℝ)) ztgv43)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (230 : ℝ)) ztgv44)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (293 : ℝ)) ztgv45)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (309 : ℝ)) ztgv46)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (398 : ℝ)) ztgv47)
      · refine le_trans ?_ (ztgTrio_concave_4 _ _ _ _ _ hhp02 (2 * 2) (2 * hminus * (2 * hminus)) _ hs4l hs4u hab2)
        refine le_min ?_ ?_
        all_goals
          refine le_trans ?_ (ztgTrio_concave_5 _ _ _ _ _ hhm2 (2 * 2) (2 * hminus * (2 * hminus)) _ hs5l hs5u hab2)
          refine le_min ?_ ?_
        all_goals
          refine le_trans ?_ (ztgTrio_concave_6 _ _ _ _ _ (by norm_num) (2 * 2) (2 * hminus * (2 * hminus)) _ hs6l hs6u hab2)
          refine le_min ?_ ?_
          all_goals first
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (262 : ℝ)) ztgv56)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (299 : ℝ)) ztgv57)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (323 : ℝ)) ztgv58)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (404 : ℝ)) ztgv59)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (317 : ℝ)) ztgv60)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (401 : ℝ)) ztgv61)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (417 : ℝ)) ztgv62)
          | (exact le_trans (by norm_num : (96:ℝ) ≤ (536 : ℝ)) ztgv63)
    have e1 : min (deltaX (y1*y1) (y2*y2) 7.02674064 (y4*y4) (y5*y5) (y6*y6))
        (deltaX (y1*y1) (y2*y2) 8 (y4*y4) (y5*y5) (y6*y6))
        ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
      ztgTrio_concave_3 _ _ _ _ _ h6p 7.02674064 8 (y3*y3) h3ge hs3u h38
    have hval : (96:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
      le_trans b2 e1
    unfold deltaY
    linarith


/-! ## Axiom audit -/


#print axioms ztgTrio_concave_1
#print axioms ztgTrio_concave_2
#print axioms ztgTrio_concave_3
#print axioms ztgTrio_concave_4
#print axioms ztgTrio_concave_5
#print axioms ztgTrio_concave_6
#print axioms ztgTrio1000_deltaY_pos
#print axioms ztgcTrio_f0
#print axioms ztgcTrio_f1
#print axioms ztgcTrio_f2
#print axioms ztgcTrio_f3
#print axioms ztgcTrio_f4
#print axioms ztgcTrio_f5
#print axioms ztgcTrio_f6
#print axioms ztgcTrio_f7
#print axioms ztgcTrio_f8
#print axioms ztgcTrio_f9
#print axioms ztgcTrio_f10
#print axioms ztgcTrio_f11
#print axioms ztgcTrio_f12
#print axioms ztgcTrio_f13
#print axioms ztgcTrio_f14
#print axioms ztgcTrio_f15
#print axioms ztgcTrio_f16
#print axioms ztgcTrio_f17
#print axioms ztgcTrio_f18
#print axioms ztgcTrio_f19
#print axioms ztgcTrio_f20
#print axioms ztgcTrio_f21
#print axioms ztgcTrio_f22
#print axioms ztgcTrio_f23
#print axioms ztgcTrio_f24
#print axioms ztgcTrio_f25
#print axioms ztgcTrio_f26
#print axioms ztgcTrio_f27
#print axioms ztgcTrio_f28
#print axioms ztgcTrio_f29
#print axioms ztgcTrio_f30
#print axioms ztgcTrio_f31
#print axioms ztgcTrio_f32
#print axioms ztgcTrio_f33
#print axioms ztgcTrio_f34
#print axioms ztgcTrio_f35
#print axioms ztgcTrio_f36
#print axioms ztgcTrio_f37
#print axioms ztgcTrio_f38
#print axioms ztgcTrio_f39
#print axioms ztgcTrio_f40
#print axioms ztgcTrio_f41
#print axioms ztgv0
#print axioms ztgv1
#print axioms ztgv2
#print axioms ztgv3
#print axioms ztgv4
#print axioms ztgv5
#print axioms ztgv6
#print axioms ztgv7
#print axioms ztgv8
#print axioms ztgv9
#print axioms ztgv10
#print axioms ztgv11
#print axioms ztgv12
#print axioms ztgv13
#print axioms ztgv14
#print axioms ztgv15
#print axioms ztgv16
#print axioms ztgv17
#print axioms ztgv18
#print axioms ztgv19
#print axioms ztgv20
#print axioms ztgv21
#print axioms ztgv22
#print axioms ztgv23
#print axioms ztgv24
#print axioms ztgv25
#print axioms ztgv26
#print axioms ztgv27
#print axioms ztgv28
#print axioms ztgv29
#print axioms ztgv30
#print axioms ztgv31
#print axioms ztgv32
#print axioms ztgv33
#print axioms ztgv34
#print axioms ztgv35
#print axioms ztgv36
#print axioms ztgv37
#print axioms ztgv38
#print axioms ztgv39
#print axioms ztgv40
#print axioms ztgv41
#print axioms ztgv42
#print axioms ztgv43
#print axioms ztgv44
#print axioms ztgv45
#print axioms ztgv46
#print axioms ztgv47
#print axioms ztgv48
#print axioms ztgv49
#print axioms ztgv50
#print axioms ztgv51
#print axioms ztgv52
#print axioms ztgv53
#print axioms ztgv54
#print axioms ztgv55
#print axioms ztgv56
#print axioms ztgv57
#print axioms ztgv58
#print axioms ztgv59
#print axioms ztgv60
#print axioms ztgv61
#print axioms ztgv62
#print axioms ztgv63


end Kepler.Text
