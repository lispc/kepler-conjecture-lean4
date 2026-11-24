/-
Kepler.Text.ZTGTrioCornerF — lane `ztg-joint6-trio-w1`, M3: the corner-library factor envelopes (polynomial-in-`hminus` bodies of the 442-atom/36-corner alphabet over `hminus ∈ [1.23175, 1.23176]`).

Machine-generated (`trio_gen_corners.py`); envelopes self-verified at three
`hminus` samples; branch-1 and Taylor feasibility checked per bracket; every
declaration axiom-audited; no `sorry`/`axiom`/`native_decide`.
-/
import Kepler.Text.ZTGTrioWide

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route


/-! ## Factor envelopes -/

theorem ztgcTrioF_f0 : ((4927/4000 : ℝ)) ≤ hminus ∧ hminus ≤ ((15397/12500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  constructor <;> linarith [hh.1, hh.2]

theorem ztgcTrioF_f1 : ((-708354684284159/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ∧ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ≤ ((-8443717014567343/3051757812500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f2 : ((-59531543112959/128000000000000 : ℝ)) ≤ ((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ∧ ((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ≤ ((-11348684879561863/24414062500000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f3 : ((106404509199/16000000 : ℝ)) ≤ ((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ)) ∧ ((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ)) ≤ ((1039129749879/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f4 : ((5027864199/16000000 : ℝ)) ≤ ((1031/1 : ℝ)) * hminus ^ 2 + ((-1250/1 : ℝ)) ∧ ((1031/1 : ℝ)) * hminus ^ 2 + ((-1250/1 : ℝ)) ≤ ((49104204879/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f5 : ((16275329/8000000 : ℝ)) ≤ ((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ∧ ((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ≤ ((158942609/78125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f6 : ((-440326912615723395864423/16384000000000000 : ℝ)) ≤ ((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ)) ∧ ((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ)) ≤ ((-2099441003262916470377981913/78125000000000000000 : ℝ)) := by
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

theorem ztgcTrioF_f7 : ((404092827472641/51200000000 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 4 + ((-5000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 4 + ((-5000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ)) ≤ ((154158886344391899/19531250000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f8 : ((-17320510586075924471/640000000000 : ℝ)) ≤ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ)) ∧ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ)) ≤ ((-6765499111666776491/250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f9 : ((-26910646986908903/1024000000 : ℝ)) ≤ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ)) ∧ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ)) ≤ ((-821208270778013077/31250000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f10 : ((66227587/6400 : ℝ)) ≤ ((7500/1 : ℝ)) * hminus ^ 2 + ((-1031/1 : ℝ)) ∧ ((7500/1 : ℝ)) * hminus ^ 2 + ((-1031/1 : ℝ)) ≤ ((646765327/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f11 : ((-461232446970007658059623/163840000 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ)) ≤ ((-2199120257481218179362356913/781250000000 : ℝ)) := by
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

theorem ztgcTrioF_f12 : ((425735727952641/5120000 : ℝ)) ≤ ((50000000/1 : ℝ)) * hminus ^ 4 + ((-50000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ)) ∧ ((50000000/1 : ℝ)) * hminus ^ 4 + ((-50000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ)) ≤ ((162414997672516899/1953125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f13 : ((-18184725288130442999/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ)) ≤ ((-14206139925377238607/5000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f14 : ((69386322751/800 : ℝ)) ≤ ((54380000/1 : ℝ)) * hminus ^ 2 + ((4227129/1 : ℝ)) ∧ ((54380000/1 : ℝ)) * hminus ^ 2 + ((4227129/1 : ℝ)) ≤ ((1355222548367/15625 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f15 : ((-17962291948808582903/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ)) ≤ ((-14032382534441894857/5000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f16 : ((1723323739/16 : ℝ)) ≤ ((75000000/1 : ℝ)) * hminus ^ 2 + ((-6082871/1 : ℝ)) ∧ ((75000000/1 : ℝ)) * hminus ^ 2 + ((-6082871/1 : ℝ)) ≤ ((2692739533/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f17 : ((-7724671/16000000 : ℝ)) ≤ hminus ^ 2 + ((-2/1 : ℝ)) ∧ hminus ^ 2 + ((-2/1 : ℝ)) ≤ ((-75432391/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f18 : ((-11432831/16000000 : ℝ)) ≤ hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ)) ∧ hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ)) ≤ ((-223286657/312500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f19 : ((40275329/16000000 : ℝ)) ≤ hminus ^ 2 + ((1/1 : ℝ)) ∧ hminus ^ 2 + ((1/1 : ℝ)) ≤ ((393317609/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f20 : ((27983329/16000000 : ℝ)) ≤ hminus ^ 2 + hminus + ((-1/1 : ℝ)) ∧ hminus ^ 2 + hminus + ((-1/1 : ℝ)) ≤ ((273280109/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f21 : ((275329/8000000 : ℝ)) ≤ ((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ)) ∧ ((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ)) ≤ ((2692609/78125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f22 : ((-12538703121197844471/640000000000 : ℝ)) ≤ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ)) ∧ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ)) ≤ ((-4897650806901151491/250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f23 : ((-23724671/16000000 : ℝ)) ≤ hminus ^ 2 + ((-3/1 : ℝ)) ∧ hminus ^ 2 + ((-3/1 : ℝ)) ≤ ((-231682391/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f24 : ((-557929084284159/102400000000 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ)) ≤ ((-6650504123942343/1220703125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f25 : ((-514643283324159/10240000 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ)) ≤ ((-12268994331869061/244140625 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f26 : ((-452354684284159/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ∧ hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ≤ ((-5391959202067343/3051757812500000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f27 : ((-68538557820159/51200000000 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 4 + ((-7500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 4 + ((-7500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ≤ ((-52268952164731827/39062500000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f28 : ((-6435702949/8000000 : ℝ)) ≤ ((438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ∧ ((438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ≤ ((-62847818629/78125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f29 : ((14873729/6400 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ≤ ((145255109/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f30 : ((-4425471/3200 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ)) ≤ ((-43213641/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f31 : ((-11884671/320000 : ℝ)) ≤ ((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ)) ∧ ((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ)) ≤ ((-116057391/3125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f32 : ((28435329/320000 : ℝ)) ≤ ((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ)) ∧ ((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ)) ≤ ((277692609/3125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f33 : ((19574529/3200 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ≤ ((191161359/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f34 : ((-191871/6400 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 2 + ((-3823/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 2 + ((-3823/1 : ℝ)) ≤ ((-1869891/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f35 : ((-2064943011869580671/102400000000 : ℝ)) ≤ ((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ)) ∧ ((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ)) ≤ ((-787655626205065584119/39062500000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f36 : ((1676929/6400 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 2 + ((-3531/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 2 + ((-3531/1 : ℝ)) ≤ ((16380109/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f37 : ((-9289178517726439/512000000 : ℝ)) ≤ ((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ)) ∧ ((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ)) ≤ ((-566912360882198029/31250000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f38 : ((-925087271/64 : ℝ)) ≤ ((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ)) ∧ ((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ)) ≤ ((-361358366/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f39 : ((-26527871/12800 : ℝ)) ≤ ((1250/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ)) ∧ ((1250/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ)) ≤ ((-259057391/125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f40 : ((-8965442382159775166471/4000000 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ)) ≤ ((-89650153266829150631/40000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f41 : ((-730830839/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-83607129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-83607129/1 : ℝ)) ≤ ((-1141907789/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f42 : ((-920815801724159/40960000 : ℝ)) ≤ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ)) ∧ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ)) ≤ ((-10976450901286093/488281250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f43 : ((-33126271/6400 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ)) ≤ ((-323494891/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f44 : ((-17894591750366439/1024000000 : ℝ)) ≤ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ)) ∧ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ)) ≤ ((-1092135479046260529/62500000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f45 : ((-17126271/6400 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ)) ≤ ((-167244891/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f46 : ((-90181458300159/5120000 : ℝ)) ≤ ((50000000/1 : ℝ)) * hminus ^ 4 + ((-75000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ∧ ((50000000/1 : ℝ)) * hminus ^ 4 + ((-75000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ≤ ((-68781174820981827/3906250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f47 : ((-9817406149/800 : ℝ)) ≤ ((4380000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ∧ ((4380000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ≤ ((-191744527883/15625 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f48 : ((304209161/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ≤ ((475342211/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f49 : ((-144453807/8 : ℝ)) ≤ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ)) ∧ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ)) ≤ ((-451387353/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f50 : ((-12931071/3200 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ)) ≤ ((-126276141/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f51 : ((29481729/3200 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ)) ≤ ((287911359/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f52 : ((455546193/8 : ℝ)) ≤ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ∧ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ≤ ((1423612647/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f53 : ((-27341463/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-39639043/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-39639043/1 : ℝ)) ≤ ((-42705639/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f54 : ((-695195943501415281959/16000000 : ℝ)) ≤ ((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ)) ∧ ((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ)) ≤ ((-1086166294327255536209/25000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f55 : ((-25710839/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-39537129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-39537129/1 : ℝ)) ≤ ((-40157789/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f56 : ((-6377305364574283639/3200 : ℝ)) ≤ ((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ)) ∧ ((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ)) ≤ ((-9963647976108854089/5000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f57 : ((-593249339859323279/256 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ)) ≤ ((-1448294953112969279/625 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f58 : ((-895790839/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ)) ≤ ((-1399657789/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f59 : ((-11301091292245832439/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ)) ≤ ((-17656909518720649089/10000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f60 : ((-495790839/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ)) ≤ ((-774657789/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f61 : ((328880027472641/128000000000000 : ℝ)) ≤ ((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ∧ ((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ)) ≤ ((125467480094391899/48828125000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f62 : ((54252619551/8000000 : ℝ)) ≤ ((5438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ∧ ((5438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ≤ ((529821203871/78125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f63 : ((56825987/16000000 : ℝ)) ≤ ((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ∧ ((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ)) ≤ ((554952827/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f64 : ((31424387/6400 : ℝ)) ≤ ((7500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ)) ∧ ((7500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ)) ≤ ((306890327/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f65 : ((-20904885022811367/2560000000000 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 4 + ((-14407/1 : ℝ)) * hminus ^ 2 + ((7938/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 4 + ((-14407/1 : ℝ)) * hminus ^ 2 + ((7938/1 : ℝ)) ≤ ((-1275848267151729279/156250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f66 : ((-26460296251548903/1024000000 : ℝ)) ≤ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-38595000/1 : ℝ)) * hminus ^ 2 + ((18330461/1 : ℝ)) ∧ ((6250000/1 : ℝ)) * hminus ^ 4 + ((-38595000/1 : ℝ)) * hminus ^ 2 + ((18330461/1 : ℝ)) ≤ ((-807459845485044327/31250000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f67 : ((11574529/3200 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ)) ≤ ((113036359/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f68 : ((30873729/6400 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 2 + ((1031/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 2 + ((1031/1 : ℝ)) ≤ ((301505109/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f69 : ((-260750839/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-54227129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-54227129/1 : ℝ)) ≤ ((-407407789/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f70 : ((-26933807/8 : ℝ)) ≤ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-79227129/1 : ℝ)) ∧ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-79227129/1 : ℝ)) ≤ ((-84137353/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f71 : ((674517289/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((4227129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((4227129/1 : ℝ)) ≤ ((1053948661/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f72 : ((656504181751041/40960000 : ℝ)) ≤ ((6250000/1 : ℝ)) * hminus ^ 4 + ((7345000/1 : ℝ)) * hminus ^ 2 + ((-9502961/1 : ℝ)) ∧ ((6250000/1 : ℝ)) * hminus ^ 4 + ((7345000/1 : ℝ)) * hminus ^ 2 + ((-9502961/1 : ℝ)) ≤ ((62611649533351881/3906250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f73 : ((143226152901/6400 : ℝ)) ≤ ((16172500/1 : ℝ)) * hminus ^ 2 + ((-2157961/1 : ℝ)) ∧ ((16172500/1 : ℝ)) * hminus ^ 2 + ((-2157961/1 : ℝ)) ≤ ((1398717800121/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f74 : ((717975611/16 : ℝ)) ≤ ((75000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ)) ∧ ((75000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ)) ≤ ((1121883083/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f75 : ((-13253427201311622903/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3813106450000000/1 : ℝ)) * hminus ^ 2 + ((2275821594592641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3813106450000000/1 : ℝ)) * hminus ^ 2 + ((2275821594592641/1 : ℝ)) ≤ ((-10353536714257519857/5000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f76 : ((-17004482099208582903/6400 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-4070856450000000/1 : ℝ)) * hminus ^ 2 + ((2080785994602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-4070856450000000/1 : ℝ)) * hminus ^ 2 + ((2080785994602641/1 : ℝ)) ≤ ((-13284016604754394857/5000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f77 : ((255546193/8 : ℝ)) ≤ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-43917129/1 : ℝ)) ∧ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-43917129/1 : ℝ)) ≤ ((798612647/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f78 : ((539249161/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-4227129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-4227129/1 : ℝ)) ≤ ((842592211/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f79 : ((704209161/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((6082871/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((6082871/1 : ℝ)) ≤ ((1100342211/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f80 : ((401932032736477329/256 : ℝ)) ≤ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((945856450000000/1 : ℝ)) * hminus ^ 2 + ((-1303714219602641/1 : ℝ)) ∧ ((625000000000000/1 : ℝ)) * hminus ^ 4 + ((945856450000000/1 : ℝ)) * hminus ^ 2 + ((-1303714219602641/1 : ℝ)) ≤ ((981323140774891671/625 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f81 : ((3817341363146967/16 : ℝ)) ≤ ((209311175000000/1 : ℝ)) * hminus ^ 2 + ((-78984767084663/1 : ℝ)) ∧ ((209311175000000/1 : ℝ)) * hminus ^ 2 + ((-78984767084663/1 : ℝ)) ≤ ((5964724789960317/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f82 : ((36098925191618769/16 : ℝ)) ≤ ((1722928225000000/1 : ℝ)) * hminus ^ 2 + ((-357857769602641/1 : ℝ)) ∧ ((1722928225000000/1 : ℝ)) * hminus ^ 2 + ((-357857769602641/1 : ℝ)) ≤ ((56405631724632219/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f83 : ((927/4000 : ℝ)) ≤ hminus + ((-1/1 : ℝ)) ∧ hminus + ((-1/1 : ℝ)) ≤ ((2897/12500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  constructor <;> linarith [hh.1, hh.2]

theorem ztgcTrioF_f84 : ((8927/4000 : ℝ)) ≤ hminus + ((1/1 : ℝ)) ∧ hminus + ((1/1 : ℝ)) ≤ ((27897/12500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  constructor <;> linarith [hh.1, hh.2]

theorem ztgcTrioF_f85 : ((-113/80 : ℝ)) ≤ ((50/1 : ℝ)) * hminus + ((-63/1 : ℝ)) ∧ ((50/1 : ℝ)) * hminus + ((-63/1 : ℝ)) ≤ ((-353/250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  constructor <;> linarith [hh.1, hh.2]

theorem ztgcTrioF_f86 : ((9967/80 : ℝ)) ≤ ((50/1 : ℝ)) * hminus + ((63/1 : ℝ)) ∧ ((50/1 : ℝ)) * hminus + ((63/1 : ℝ)) ≤ ((31147/250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  constructor <;> linarith [hh.1, hh.2]

theorem ztgcTrioF_f87 : ((3574529/3200 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ)) ≤ ((34911359/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f88 : ((17676929/6400 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 2 + ((-1031/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 2 + ((-1031/1 : ℝ)) ≤ ((172630109/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f89 : ((-1873/4 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus + ((-6627/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus + ((-6627/1 : ℝ)) ≤ ((-2341/5 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  constructor <;> linarith [hh.1, hh.2]

theorem ztgcTrioF_f90 : ((51143/4 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus + ((6627/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus + ((6627/1 : ℝ)) ≤ ((63929/5 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  constructor <;> linarith [hh.1, hh.2]

theorem ztgcTrioF_f91 : ((55546193/8 : ℝ)) ≤ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ)) ∧ ((50000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ)) ≤ ((173612647/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f92 : ((509557289/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-6082871/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-6082871/1 : ℝ)) ≤ ((796198661/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f93 : ((7340929/12800 : ℝ)) ≤ ((1250/1 : ℝ)) * hminus ^ 2 + ((-1323/1 : ℝ)) ∧ ((1250/1 : ℝ)) * hminus ^ 2 + ((-1323/1 : ℝ)) ≤ ((71692609/125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f94 : ((-151503484284159/204800000000 : ℝ)) ≤ ((1250/1 : ℝ)) * hminus ^ 4 + ((-5000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ)) ∧ ((1250/1 : ℝ)) * hminus ^ 4 + ((-5000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ)) ≤ ((-1805533420817343/2441406250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f95 : ((138433849/32 : ℝ)) ≤ ((12500000/1 : ℝ)) * hminus ^ 2 + ((-14639043/1 : ℝ)) ∧ ((12500000/1 : ℝ)) * hminus ^ 2 + ((-14639043/1 : ℝ)) ≤ ((108159143/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f96 : ((-64931882364159/20480000 : ℝ)) ≤ ((12500000/1 : ℝ)) * hminus ^ 4 + ((-50000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ)) ∧ ((12500000/1 : ℝ)) * hminus ^ 4 + ((-50000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ)) ≤ ((-773519504801718/244140625 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f97 : ((40825987/16000000 : ℝ)) ≤ ((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ)) ∧ ((3/1 : ℝ)) * hminus ^ 2 + ((-2/1 : ℝ)) ≤ ((398702827/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f98 : ((-17014633079006439/2560000000000 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 4 + ((-11469/1 : ℝ)) * hminus ^ 2 + ((5000/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 4 + ((-11469/1 : ℝ)) * hminus ^ 2 + ((5000/1 : ℝ)) ≤ ((-1038417440960323029/156250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f99 : ((-840766254869759/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ∧ hminus ^ 4 + ((-5/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ≤ ((-320707544319670601/97656250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f100 : ((9927225450273561/2560000000000 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 4 + ((-6469/1 : ℝ)) * hminus ^ 2 + ((7938/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 4 + ((-6469/1 : ℝ)) * hminus ^ 2 + ((7938/1 : ℝ)) ≤ ((605963857867801971/156250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f101 : ((221729161/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-24072129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((-24072129/1 : ℝ)) ≤ ((346467211/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f102 : ((11501051399/3200 : ℝ)) ≤ ((5155000/1 : ℝ)) * hminus ^ 2 + ((-4227129/1 : ℝ)) ∧ ((5155000/1 : ℝ)) * hminus ^ 2 + ((-4227129/1 : ℝ)) ≤ ((112318923629/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f103 : ((16547803979553561/2560000000000 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 4 + ((-1469/1 : ℝ)) * hminus ^ 2 + ((2938/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 4 + ((-1469/1 : ℝ)) * hminus ^ 2 + ((2938/1 : ℝ)) ≤ ((1010032656695926971/156250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f104 : ((43078529/12800 : ℝ)) ≤ ((1250/1 : ℝ)) * hminus ^ 2 + ((1469/1 : ℝ)) ∧ ((1250/1 : ℝ)) * hminus ^ 2 + ((1469/1 : ℝ)) ≤ ((420692609/125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f105 : ((132724186699/16000000 : ℝ)) ≤ ((3531/1 : ℝ)) * hminus ^ 2 + ((2938/1 : ℝ)) ∧ ((3531/1 : ℝ)) * hminus ^ 2 + ((2938/1 : ℝ)) ≤ ((1296148227379/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f106 : ((72035864199/16000000 : ℝ)) ≤ ((1031/1 : ℝ)) * hminus ^ 2 + ((2938/1 : ℝ)) ∧ ((1031/1 : ℝ)) * hminus ^ 2 + ((2938/1 : ℝ)) ≤ ((703479204879/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f107 : ((6531031052697265161/160000000000 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 4 + ((-68917129/1 : ℝ)) * hminus ^ 2 + ((87834258/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 4 + ((-68917129/1 : ℝ)) * hminus ^ 2 + ((87834258/1 : ℝ)) ≤ ((10205627675877940911/250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f108 : ((10668892633497265161/160000000000 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 4 + ((-18917129/1 : ℝ)) * hminus ^ 2 + ((37834258/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 4 + ((-18917129/1 : ℝ)) * hminus ^ 2 + ((37834258/1 : ℝ)) ≤ ((16670728457127940911/250000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f109 : ((158516629399937/16000000 : ℝ)) ≤ ((2967553/1 : ℝ)) * hminus ^ 2 + ((5404894/1 : ℝ)) ∧ ((2967553/1 : ℝ)) * hminus ^ 2 + ((5404894/1 : ℝ)) ≤ ((1548025381790777/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f110 : ((1359895047789559/16000000 : ℝ)) ≤ ((31082871/1 : ℝ)) * hminus ^ 2 + ((37834258/1 : ℝ)) ∧ ((31082871/1 : ℝ)) * hminus ^ 2 + ((37834258/1 : ℝ)) ≤ ((13280344721325439/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f111 : ((753011822789559/16000000 : ℝ)) ≤ ((6082871/1 : ℝ)) * hminus ^ 2 + ((37834258/1 : ℝ)) ∧ ((6082871/1 : ℝ)) * hminus ^ 2 + ((37834258/1 : ℝ)) ≤ ((7353654496325439/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f112 : ((324468456887041/256000000000000 : ℝ)) ≤ hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ∧ hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ)) ≤ ((61893502620438137/48828125000000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f113 : ((-64665185401/6400 : ℝ)) ≤ ((2577500/1 : ℝ)) * hminus ^ 2 + ((-14014539/1 : ℝ)) ∧ ((2577500/1 : ℝ)) * hminus ^ 2 + ((-14014539/1 : ℝ)) ≤ ((-631491982621/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f114 : ((-1686360355009/16 : ℝ)) ≤ ((25775000000/1 : ℝ)) * hminus ^ 2 + ((-144503559999/1 : ℝ)) ∧ ((25775000000/1 : ℝ)) * hminus ^ 2 + ((-144503559999/1 : ℝ)) ≤ ((-2634922180459/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f115 : ((288440398058241/204800000000 : ℝ)) ≤ ((1250/1 : ℝ)) * hminus ^ 4 + ((-1469/1 : ℝ)) ∧ ((1250/1 : ℝ)) * hminus ^ 4 + ((-1469/1 : ℝ)) ≤ ((27509644986976881/19531250000000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f116 : ((5472129/12800 : ℝ)) ≤ ((1250/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ∧ ((1250/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ)) ≤ ((53442609/125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f117 : ((201868796138241/20480000 : ℝ)) ≤ ((12500000/1 : ℝ)) * hminus ^ 4 + ((-18917129/1 : ℝ)) ∧ ((12500000/1 : ℝ)) * hminus ^ 4 + ((-18917129/1 : ℝ)) ≤ ((19253533658851881/1953125000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hp3 : ((119604545983/64000000000 : ℝ)) ≤ hminus ^ 3 ∧ hminus ^ 3 ≤ ((3650129975773/1953125000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hh.1, hh.2]
  have hp4 : ((589291598058241/256000000000000 : ℝ)) ≤ hminus ^ 4 ∧ hminus ^ 4 ≤ ((56201051236976881/24414062500000000 : ℝ)) := by
    constructor <;> nlinarith [hp2.1, hp2.2, hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2, hp3.1, hp3.2, hp4.1, hp4.2]

theorem ztgcTrioF_f118 : ((1535097/32 : ℝ)) ≤ ((12500000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ∧ ((12500000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ)) ≤ ((1206993/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f119 : ((20976129/3200 : ℝ)) ≤ ((5000/1 : ℝ)) * hminus ^ 2 + ((-1031/1 : ℝ)) ∧ ((5000/1 : ℝ)) * hminus ^ 2 + ((-1031/1 : ℝ)) ≤ ((204848859/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f120 : ((106041830401/6400 : ℝ)) ≤ ((9922500/1 : ℝ)) * hminus ^ 2 + ((1514539/1 : ℝ)) ∧ ((9922500/1 : ℝ)) * hminus ^ 2 + ((1514539/1 : ℝ)) ≤ ((1035580027621/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f121 : ((388682354287/16 : ℝ)) ≤ ((14175000000/1 : ℝ)) * hminus ^ 2 + ((2786222857/1 : ℝ)) ∧ ((14175000000/1 : ℝ)) * hminus ^ 2 + ((2786222857/1 : ℝ)) ≤ ((607324908637/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f122 : ((33676929/6400 : ℝ)) ≤ ((2500/1 : ℝ)) * hminus ^ 2 + ((1469/1 : ℝ)) ∧ ((2500/1 : ℝ)) * hminus ^ 2 + ((1469/1 : ℝ)) ≤ ((328880109/62500 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f123 : ((909557289/16 : ℝ)) ≤ ((25000000/1 : ℝ)) * hminus ^ 2 + ((18917129/1 : ℝ)) ∧ ((25000000/1 : ℝ)) * hminus ^ 2 + ((18917129/1 : ℝ)) ≤ ((1421198661/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f124 : ((-159102023/32 : ℝ)) ≤ ((12500000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ)) ∧ ((12500000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ)) ≤ ((-124290757/25 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f125 : ((-108155104373/2 : ℝ)) ≤ ((125000000000/1 : ℝ)) * hminus ^ 2 + ((-243728559999/1 : ℝ)) ∧ ((125000000000/1 : ℝ)) * hminus ^ 2 + ((-243728559999/1 : ℝ)) ≤ ((-54074472799/1 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f126 : ((-54972135801/16000000 : ℝ)) ≤ ((1031/1 : ℝ)) * hminus ^ 2 + ((-5000/1 : ℝ)) ∧ ((1031/1 : ℝ)) * hminus ^ 2 + ((-5000/1 : ℝ)) ≤ ((-536833295121/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f127 : ((49340780801/16000000 : ℝ)) ≤ ((3969/1 : ℝ)) * hminus ^ 2 + ((-2938/1 : ℝ)) ∧ ((3969/1 : ℝ)) * hminus ^ 2 + ((-2938/1 : ℝ)) ≤ ((481858840121/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f128 : ((5116281143/3200 : ℝ)) ≤ ((2835000/1 : ℝ)) * hminus ^ 2 + ((-2702447/1 : ℝ)) ∧ ((2835000/1 : ℝ)) * hminus ^ 2 + ((-2702447/1 : ℝ)) ≤ ((49965865553/31250 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

theorem ztgcTrioF_f129 : ((282931822789559/16000000 : ℝ)) ≤ ((6082871/1 : ℝ)) * hminus ^ 2 + ((8454258/1 : ℝ)) ∧ ((6082871/1 : ℝ)) * hminus ^ 2 + ((8454258/1 : ℝ)) ≤ ((2763029496325439/156250000 : ℝ)) := by
  have hh := Kepler.NliBanks17.nb17_hminus_bounds
  have hq := ztgc0000_hm_sq
  have hp2 : ((24275329/16000000 : ℝ)) ≤ hminus ^ 2 ∧ hminus ^ 2 ≤ ((237067609/156250000 : ℝ)) := by
    constructor <;> nlinarith [hq.1, hq.2]
  constructor <;> linarith [hh.1, hh.2, hq.1, hq.2, hp2.1, hp2.2]

/-! ## Axiom audit -/

#print axioms ztgcTrioF_f0
#print axioms ztgcTrioF_f1
#print axioms ztgcTrioF_f2
#print axioms ztgcTrioF_f3
#print axioms ztgcTrioF_f4
#print axioms ztgcTrioF_f5
#print axioms ztgcTrioF_f6
#print axioms ztgcTrioF_f7
#print axioms ztgcTrioF_f8
#print axioms ztgcTrioF_f9
#print axioms ztgcTrioF_f10
#print axioms ztgcTrioF_f11
#print axioms ztgcTrioF_f12
#print axioms ztgcTrioF_f13
#print axioms ztgcTrioF_f14
#print axioms ztgcTrioF_f15
#print axioms ztgcTrioF_f16
#print axioms ztgcTrioF_f17
#print axioms ztgcTrioF_f18
#print axioms ztgcTrioF_f19
#print axioms ztgcTrioF_f20
#print axioms ztgcTrioF_f21
#print axioms ztgcTrioF_f22
#print axioms ztgcTrioF_f23
#print axioms ztgcTrioF_f24
#print axioms ztgcTrioF_f25
#print axioms ztgcTrioF_f26
#print axioms ztgcTrioF_f27
#print axioms ztgcTrioF_f28
#print axioms ztgcTrioF_f29
#print axioms ztgcTrioF_f30
#print axioms ztgcTrioF_f31
#print axioms ztgcTrioF_f32
#print axioms ztgcTrioF_f33
#print axioms ztgcTrioF_f34
#print axioms ztgcTrioF_f35
#print axioms ztgcTrioF_f36
#print axioms ztgcTrioF_f37
#print axioms ztgcTrioF_f38
#print axioms ztgcTrioF_f39
#print axioms ztgcTrioF_f40
#print axioms ztgcTrioF_f41
#print axioms ztgcTrioF_f42
#print axioms ztgcTrioF_f43
#print axioms ztgcTrioF_f44
#print axioms ztgcTrioF_f45
#print axioms ztgcTrioF_f46
#print axioms ztgcTrioF_f47
#print axioms ztgcTrioF_f48
#print axioms ztgcTrioF_f49
#print axioms ztgcTrioF_f50
#print axioms ztgcTrioF_f51
#print axioms ztgcTrioF_f52
#print axioms ztgcTrioF_f53
#print axioms ztgcTrioF_f54
#print axioms ztgcTrioF_f55
#print axioms ztgcTrioF_f56
#print axioms ztgcTrioF_f57
#print axioms ztgcTrioF_f58
#print axioms ztgcTrioF_f59
#print axioms ztgcTrioF_f60
#print axioms ztgcTrioF_f61
#print axioms ztgcTrioF_f62
#print axioms ztgcTrioF_f63
#print axioms ztgcTrioF_f64
#print axioms ztgcTrioF_f65
#print axioms ztgcTrioF_f66
#print axioms ztgcTrioF_f67
#print axioms ztgcTrioF_f68
#print axioms ztgcTrioF_f69
#print axioms ztgcTrioF_f70
#print axioms ztgcTrioF_f71
#print axioms ztgcTrioF_f72
#print axioms ztgcTrioF_f73
#print axioms ztgcTrioF_f74
#print axioms ztgcTrioF_f75
#print axioms ztgcTrioF_f76
#print axioms ztgcTrioF_f77
#print axioms ztgcTrioF_f78
#print axioms ztgcTrioF_f79
#print axioms ztgcTrioF_f80
#print axioms ztgcTrioF_f81
#print axioms ztgcTrioF_f82
#print axioms ztgcTrioF_f83
#print axioms ztgcTrioF_f84
#print axioms ztgcTrioF_f85
#print axioms ztgcTrioF_f86
#print axioms ztgcTrioF_f87
#print axioms ztgcTrioF_f88
#print axioms ztgcTrioF_f89
#print axioms ztgcTrioF_f90
#print axioms ztgcTrioF_f91
#print axioms ztgcTrioF_f92
#print axioms ztgcTrioF_f93
#print axioms ztgcTrioF_f94
#print axioms ztgcTrioF_f95
#print axioms ztgcTrioF_f96
#print axioms ztgcTrioF_f97
#print axioms ztgcTrioF_f98
#print axioms ztgcTrioF_f99
#print axioms ztgcTrioF_f100
#print axioms ztgcTrioF_f101
#print axioms ztgcTrioF_f102
#print axioms ztgcTrioF_f103
#print axioms ztgcTrioF_f104
#print axioms ztgcTrioF_f105
#print axioms ztgcTrioF_f106
#print axioms ztgcTrioF_f107
#print axioms ztgcTrioF_f108
#print axioms ztgcTrioF_f109
#print axioms ztgcTrioF_f110
#print axioms ztgcTrioF_f111
#print axioms ztgcTrioF_f112
#print axioms ztgcTrioF_f113
#print axioms ztgcTrioF_f114
#print axioms ztgcTrioF_f115
#print axioms ztgcTrioF_f116
#print axioms ztgcTrioF_f117
#print axioms ztgcTrioF_f118
#print axioms ztgcTrioF_f119
#print axioms ztgcTrioF_f120
#print axioms ztgcTrioF_f121
#print axioms ztgcTrioF_f122
#print axioms ztgcTrioF_f123
#print axioms ztgcTrioF_f124
#print axioms ztgcTrioF_f125
#print axioms ztgcTrioF_f126
#print axioms ztgcTrioF_f127
#print axioms ztgcTrioF_f128
#print axioms ztgcTrioF_f129

end Kepler.Text
