/-
Kepler.Text.ZTGTrioCornerTHMa — lane `ztg-joint6-trio-w1`, M3: dihY brackets at the HM orbit representatives of the trio corner alphabet (chunk 1 of 3).

Machine-generated (`trio_gen_corners.py`); envelopes self-verified at three
`hminus` samples; branch-1 and Taylor feasibility checked per bracket; every
declaration axiom-audited; no `sorry`/`axiom`/`native_decide`.
-/
import Kepler.Text.ZTGTrioCornerTR
import Kepler.Text.ZTGTrioSym

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route


/-! ## HM representative brackets (chunk 1) -/

theorem ztgcTrioT_t0 :
    ((1478911121900757550731/1000000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) ≤ ((369741049154733427319/250000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp5.1, le_trans hp5.2 (by norm_num)⟩
  have hs1 : ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) := by norm_num
  have hs2 : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((2019052366213842803823662138226133/25000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus))) ≤ ((2019052366213842803823662138226133/25000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((11348684879561863/1525878906250000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((59531543112959/8000000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    have hp1 : ((11348684879561863/1525878906250000 : ℝ)) ≤ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((59531543112959/8000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f2
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-59531543112959/8000000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ≤ ((-11348684879561863/1525878906250000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| ≤ ((59531543112959/8000000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-11348684879561863/1525878906250000 : ℝ)) < ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus))) ≤ -((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus))) < ((-59531543112959/8000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) < ((-59531543112959/8000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-11348684879561863/1525878906250000 : ℝ)) ≤ ((-185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ)) * ((2019052366213842803823662138226133/25000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus))) ≤ ((-185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ)) * ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) ≤ ((-59531543112959/8000000000000 : ℝ)) := by norm_num
  have harg2 : ((-744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hminus) (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ))) (lo := ((91885203854139068499/1000000000000000000000 : ℝ))) (hi := ((91885203894139068499/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ)) = -Real.arctan ((744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ)) := by rw [show ((-744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ)) = -((744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((91885203894139068499/1000000000000000000000 : ℝ)) ≤ Real.arctan ((-744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ)) ∧ Real.arctan ((-744144288911987500000000000000000/8075825431614573170645683853460711 : ℝ)) ≤ -((91885203854139068499/1000000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ))) (lo := ((91832131175962909959/1000000000000000000000 : ℝ))) (hi := ((91832131215962909959/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ)) = -Real.arctan ((185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ)) := by rw [show ((-185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ)) = -((185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((91832131215962909959/1000000000000000000000 : ℝ)) ≤ Real.arctan ((-185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ)) ∧ Real.arctan ((-185936853066741563392000000000000/2019052366213842803823662138226133 : ℝ)) ≤ -((91832131175962909959/1000000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t1 :
    ((19014701056752823593/12500000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2 ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2 ≤ ((152118104573139027401/100000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) = ((8/625 : ℝ)) * (((1031/1 : ℝ)) * hminus ^ 2 + ((-1250/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) = ((15876/390625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) = ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((10251944733052439088399/1562500000000000000 : ℝ)) ≤ ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ∧ ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ≤ ((977739356815748217595359/149011611938476562500 : ℝ)) := by
    have hp0 : ((254016/390625 : ℝ)) ≤ ((254016/390625 : ℝ)) ∧ ((254016/390625 : ℝ)) ≤ ((254016/390625 : ℝ)) := by norm_num
    have hp1 : ((39110526/48828125 : ℝ)) ≤ ((254016/390625 : ℝ)) * (hminus) ∧ ((254016/390625 : ℝ)) * (hminus) ≤ ((977771088/1220703125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((96348780801/97656250000 : ℝ)) ≤ ((254016/390625 : ℝ)) * (hminus) * (hminus) ∧ ((254016/390625 : ℝ)) * (hminus) * (hminus) ≤ ((3763685360484/3814697265625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((10251944733052439088399/1562500000000000000 : ℝ)) ≤ ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ∧ ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ≤ ((977739356815748217595359/149011611938476562500 : ℝ)) := by
      have hf := ztgcTrioF_f3
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((10251944733052439088399/1562500000000000000 : ℝ)) := by norm_num
  have hs2 : ((977739356815748217595359/149011611938476562500 : ℝ)) ≤ ((8100307248740434814372487403538113/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2)) ≤ ((8100307248740434814372487403538113/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((5027864199/1250000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) ≤ ((49104204879/12207031250 : ℝ)) := by
    rw [hE4]
    have hp0 : ((8/625 : ℝ)) ≤ ((8/625 : ℝ)) ∧ ((8/625 : ℝ)) ≤ ((8/625 : ℝ)) := by norm_num
    have hp1 : ((5027864199/1250000000 : ℝ)) ≤ ((8/625 : ℝ)) * (((1031/1 : ℝ)) * hminus ^ 2 + ((-1250/1 : ℝ))) ∧ ((8/625 : ℝ)) * (((1031/1 : ℝ)) * hminus ^ 2 + ((-1250/1 : ℝ))) ≤ ((49104204879/12207031250 : ℝ)) := by
      have hf := ztgcTrioF_f4
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-49104204879/12207031250 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2))) ≤ ((-5027864199/1250000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2)))| ≤ ((49104204879/12207031250 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-5027864199/1250000000 : ℝ)) < ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2)) ≤ -((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2)) < ((-49104204879/12207031250 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) < ((-49104204879/12207031250 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-5027864199/1250000000 : ℝ)) ≤ ((-402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ)) * ((8100307248740434814372487403538113/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2)) ≤ ((-402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-26817443091251200000000000000000/540010066949514471599330504801283 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-26817443091251200000000000000000/540010066949514471599330504801283 : ℝ)) * ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) ≤ ((-49104204879/12207031250 : ℝ)) := by norm_num
  have harg2 : ((-26817443091251200000000000000000/540010066949514471599330504801283 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2.52 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((26817443091251200000000000000000/540010066949514471599330504801283 : ℝ))) (lo := ((4962024121467073179/100000000000000000000 : ℝ))) (hi := ((4962024125467073179/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-26817443091251200000000000000000/540010066949514471599330504801283 : ℝ)) = -Real.arctan ((26817443091251200000000000000000/540010066949514471599330504801283 : ℝ)) := by rw [show ((-26817443091251200000000000000000/540010066949514471599330504801283 : ℝ)) = -((26817443091251200000000000000000/540010066949514471599330504801283 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((4962024125467073179/100000000000000000000 : ℝ)) ≤ Real.arctan ((-26817443091251200000000000000000/540010066949514471599330504801283 : ℝ)) ∧ Real.arctan ((-26817443091251200000000000000000/540010066949514471599330504801283 : ℝ)) ≤ -((4962024121467073179/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ))) (lo := ((1984611282540253809/40000000000000000000 : ℝ))) (hi := ((1984611284140253809/40000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ)) = -Real.arctan ((402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ)) := by rw [show ((-402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ)) = -((402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((1984611284140253809/40000000000000000000 : ℝ)) ≤ Real.arctan ((-402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ)) ∧ Real.arctan ((-402229135920000000000000000000000/8100307248740434814372487403538113 : ℝ)) ≤ -((1984611282540253809/40000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t2 :
    ((2764655014254750847/1562500000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) ≤ ((353876624653296405659/200000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-16/1 : ℝ)) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((395088966058241/62500000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((602882308541630096/95367431640625 : ℝ)) := by
    have hp0 : ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) ∧ ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) := by norm_num
    have hp1 : ((315328/125 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) ≤ ((7883264/3125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((48550658/15625 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) ≤ ((30344653952/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((395088966058241/62500000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((602882308541630096/95367431640625 : ℝ)) := by
      have hf := ztgcTrioF_f5
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((395088966058241/62500000000 : ℝ)) := by norm_num
  have hs2 : ((602882308541630096/95367431640625 : ℝ)) ≤ ((795089881435653136998814356451861/10000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus))) ≤ ((795089881435653136998814356451861/10000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-16/1 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((-16/1 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    exact ⟨le_trans (by norm_num) hp0.1, le_trans hp0.2 (by norm_num)⟩
  have htlo : ((16/1 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ≤ ((16/1 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| ≤ ((16/1 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((16/1 : ℝ)) < ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus))) ≤ -((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus))) < ((16/1 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) < ((16/1 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((16/1 : ℝ)) := by norm_num
  have hnum : ((16/1 : ℝ)) ≤ ((800000000000000000000000000000000/3975368994487093386610055128668597 : ℝ)) * ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus))) ≤ ((800000000000000000000000000000000/3975368994487093386610055128668597 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((160000000000000000000000000000000/795089881435653136998814356451861 : ℝ)) := by norm_num
  have hnum2 : ((160000000000000000000000000000000/795089881435653136998814356451861 : ℝ)) * ((795089881435653136998814356451861/10000000000000000000000000000000 : ℝ)) ≤ ((16/1 : ℝ)) := by norm_num
  have harg2 : ((160000000000000000000000000000000/795089881435653136998814356451861 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((160000000000000000000000000000000/795089881435653136998814356451861 : ℝ))) (lo := ((3971657666562878457/20000000000000000000 : ℝ))) (hi := ((3971657667362878457/20000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((800000000000000000000000000000000/3975368994487093386610055128668597 : ℝ))) (lo := ((9929339771579270453/50000000000000000000 : ℝ))) (hi := ((9929339773579270453/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ≤ ((795089881435653136998814356451861/10000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) := by rw [h8]
  have htlo8 : ((16/1 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((16/1 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (Real.sqrt 8) (2 * hminus) (2 * hminus))) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ≤ -((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) < ((16/1 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) < ((16/1 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t3 :
    ((102192375561257185251/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) ≤ ((204392585632461373687/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp5.1, le_trans hp5.2 (by norm_num)⟩
  have hs1 : ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) := by norm_num
  have hs2 : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((2019052366213842803823662138226133/25000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus))) ≤ ((2019052366213842803823662138226133/25000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((395088966058241/8000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((395088966058241/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((37680144283851881/762939453125000 : ℝ)) := by
      have hf := ztgcTrioF_f5
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-37680144283851881/762939453125000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-395088966058241/8000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((37680144283851881/762939453125000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-395088966058241/8000000000000 : ℝ)) < ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus))) ≤ -((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus))) < ((-37680144283851881/762939453125000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) < ((-37680144283851881/762939453125000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-395088966058241/8000000000000 : ℝ)) ≤ ((-1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ)) * ((2019052366213842803823662138226133/25000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus))) ≤ ((-1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ)) * ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) ≤ ((-37680144283851881/762939453125000 : ℝ)) := by norm_num
  have harg2 : ((-4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ))) (lo := ((53600836927961403/97656250000000000 : ℝ))) (hi := ((53600836931867653/97656250000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ)) = -Real.arctan ((4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ)) := by rw [show ((-4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ)) = -((4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((53600836931867653/97656250000000000 : ℝ)) ≤ Real.arctan ((-4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ)) ∧ Real.arctan ((-4938811871573033746432000000000000/8075825431614573170645683853460711 : ℝ)) ≤ -((53600836927961403/97656250000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ))) (lo := ((1372083499081474377/2500000000000000000 : ℝ))) (hi := ((1372083499181474377/2500000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ)) = -Real.arctan ((1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ)) := by rw [show ((-1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ)) = -((1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((1372083499181474377/2500000000000000000 : ℝ)) ≤ Real.arctan ((-1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ)) ∧ Real.arctan ((-1234653018932003125000000000000000/2019052366213842803823662138226133 : ℝ)) ≤ -((1372083499081474377/2500000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t4 :
    ((4011623142509882223/4000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus) ∧ dihY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus) ≤ ((200585102984727969061/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((15876/625 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((15876/390625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((10251944733052439088399/1562500000000000000 : ℝ)) ≤ ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ∧ ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ≤ ((977739356815748217595359/149011611938476562500 : ℝ)) := by
    have hp0 : ((254016/390625 : ℝ)) ≤ ((254016/390625 : ℝ)) ∧ ((254016/390625 : ℝ)) ≤ ((254016/390625 : ℝ)) := by norm_num
    have hp1 : ((39110526/48828125 : ℝ)) ≤ ((254016/390625 : ℝ)) * (hminus) ∧ ((254016/390625 : ℝ)) * (hminus) ≤ ((977771088/1220703125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((96348780801/97656250000 : ℝ)) ≤ ((254016/390625 : ℝ)) * (hminus) * (hminus) ∧ ((254016/390625 : ℝ)) * (hminus) * (hminus) ≤ ((3763685360484/3814697265625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((10251944733052439088399/1562500000000000000 : ℝ)) ≤ ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ∧ ((254016/390625 : ℝ)) * (hminus) * (hminus) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ≤ ((977739356815748217595359/149011611938476562500 : ℝ)) := by
      have hf := ztgcTrioF_f3
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((10251944733052439088399/1562500000000000000 : ℝ)) := by norm_num
  have hs2 : ((977739356815748217595359/149011611938476562500 : ℝ)) ≤ ((8100307248740434814372487403538113/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus))) ≤ ((8100307248740434814372487403538113/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((64596780801/1250000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((630843215121/12207031250 : ℝ)) := by
    rw [hE4]
    have hp0 : ((15876/625 : ℝ)) ≤ ((15876/625 : ℝ)) ∧ ((15876/625 : ℝ)) ≤ ((15876/625 : ℝ)) := by norm_num
    have hp1 : ((64596780801/1250000000 : ℝ)) ≤ ((15876/625 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((15876/625 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((630843215121/12207031250 : ℝ)) := by
      have hf := ztgcTrioF_f5
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-630843215121/12207031250 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ≤ ((-64596780801/1250000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| ≤ ((630843215121/12207031250 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-64596780801/1250000000 : ℝ)) < ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus))) ≤ -((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus))) < ((-630843215121/12207031250 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) < ((-630843215121/12207031250 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-64596780801/1250000000 : ℝ)) ≤ ((-5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ)) * ((8100307248740434814372487403538113/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus))) ≤ ((-5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-38280500876083200000000000000000/60001118549946052399925611644587 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-38280500876083200000000000000000/60001118549946052399925611644587 : ℝ)) * ((1620030200848543414797991514403849/20000000000000000000000000000000 : ℝ)) ≤ ((-630843215121/12207031250 : ℝ)) := by norm_num
  have harg2 : ((-38280500876083200000000000000000/60001118549946052399925611644587 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((38280500876083200000000000000000/60001118549946052399925611644587 : ℝ))) (lo := ((14197263503185651587/25000000000000000000 : ℝ))) (hi := ((14197263504185651587/25000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-38280500876083200000000000000000/60001118549946052399925611644587 : ℝ)) = -Real.arctan ((38280500876083200000000000000000/60001118549946052399925611644587 : ℝ)) := by rw [show ((-38280500876083200000000000000000/60001118549946052399925611644587 : ℝ)) = -((38280500876083200000000000000000/60001118549946052399925611644587 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((14197263504185651587/25000000000000000000 : ℝ)) ≤ Real.arctan ((-38280500876083200000000000000000/60001118549946052399925611644587 : ℝ)) ∧ Real.arctan ((-38280500876083200000000000000000/60001118549946052399925611644587 : ℝ)) ≤ -((14197263503185651587/25000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ))) (lo := ((56787081287125677393/100000000000000000000 : ℝ))) (hi := ((56787081291125677393/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ)) = -Real.arctan ((5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ)) := by rw [show ((-5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ)) = -((5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((56787081291125677393/100000000000000000000 : ℝ)) ≤ Real.arctan ((-5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ)) ∧ Real.arctan ((-5167742464080000000000000000000000/8100307248740434814372487403538113 : ℝ)) ≤ -((56787081287125677393/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t5 :
    ((70774375122673751573/80000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) ∧ dihY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) ≤ ((110587684639245952581/125000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8) = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 = ((32/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 = ((128/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 = ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((395088966058241/62500000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((602882308541630096/95367431640625 : ℝ)) := by
    have hp0 : ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) ∧ ((2048/1 : ℝ)) ≤ ((2048/1 : ℝ)) := by norm_num
    have hp1 : ((315328/125 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) ≤ ((7883264/3125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((48550658/15625 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) ≤ ((30344653952/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((395088966058241/62500000000 : ℝ)) ≤ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((602882308541630096/95367431640625 : ℝ)) := by
      have hf := ztgcTrioF_f5
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((395088966058241/62500000000 : ℝ)) := by norm_num
  have hs2 : ((602882308541630096/95367431640625 : ℝ)) ≤ ((795089881435653136998814356451861/10000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8))) ≤ ((795089881435653136998814356451861/10000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((16275329/250000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 ≤ ((635770436/9765625 : ℝ)) := by
    rw [hE4]
    have hp0 : ((32/1 : ℝ)) ≤ ((32/1 : ℝ)) ∧ ((32/1 : ℝ)) ≤ ((32/1 : ℝ)) := by norm_num
    have hp1 : ((16275329/250000 : ℝ)) ≤ ((32/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((32/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((635770436/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f5
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-635770436/9765625 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8)) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8)) ≤ ((-16275329/250000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8))| ≤ ((635770436/9765625 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-16275329/250000 : ℝ)) < ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8))) ≤ -((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8))) < ((-635770436/9765625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) < ((-635770436/9765625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-16275329/250000 : ℝ)) ≤ ((-651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) * ((795089881435653136998814356451861/10000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8)) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8))) ≤ ((-651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) * ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) ≤ ((-635770436/9765625 : ℝ)) := by norm_num
  have harg2 : ((-3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8)) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have hshlo : Real.arctan ((3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) = Real.pi / 4 + Real.arctan (((((3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ))) - 1) / ((((3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrlo : (((((3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ))) - 1) / ((((3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ))) + 1)) = ((-720224362167093386610055128668597/7230513626807093386610055128668597 : ℝ)) := by norm_num
  have htwlo := g4v_atan_pos_bounds (x := ((720224362167093386610055128668597/7230513626807093386610055128668597 : ℝ))) (lo := ((1985630532719471701/20000000000000000000 : ℝ))) (hi := ((1985630533519471701/20000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwlo : Real.arctan ((-720224362167093386610055128668597/7230513626807093386610055128668597 : ℝ)) = -Real.arctan ((720224362167093386610055128668597/7230513626807093386610055128668597 : ℝ)) := by rw [show ((-720224362167093386610055128668597/7230513626807093386610055128668597 : ℝ)) = -((720224362167093386610055128668597/7230513626807093386610055128668597 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnglo : Real.arctan ((-3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) = -Real.arctan ((3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) := by rw [show ((-3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) = -((3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : ((-274446654704589889827/400000000000000000000 : ℝ)) ≤ Real.arctan ((-3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) ∧ Real.arctan ((-3255144632320000000000000000000000/3975368994487093386610055128668597 : ℝ)) ≤ ((-137223327344294944913/200000000000000000000 : ℝ)) := by
    rw [hnglo, hshlo, hfrlo, hgwlo]
    constructor <;> linarith [htwlo.1, htwlo.2, hp1, hp2]
  have hshhi : Real.arctan ((651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) = Real.pi / 4 + Real.arctan (((((651013160000000000000000000000000/795089881435653136998814356451861 : ℝ))) - 1) / ((((651013160000000000000000000000000/795089881435653136998814356451861 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrhi : (((((651013160000000000000000000000000/795089881435653136998814356451861 : ℝ))) - 1) / ((((651013160000000000000000000000000/795089881435653136998814356451861 : ℝ))) + 1)) = ((-144076721435653136998814356451861/1446103041435653136998814356451861 : ℝ)) := by norm_num
  have htwhi := g4v_atan_pos_bounds (x := ((144076721435653136998814356451861/1446103041435653136998814356451861 : ℝ))) (lo := ((24825828169129827757/250000000000000000000 : ℝ))) (hi := ((24825828179129827757/250000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwhi : Real.arctan ((-144076721435653136998814356451861/1446103041435653136998814356451861 : ℝ)) = -Real.arctan ((144076721435653136998814356451861/1446103041435653136998814356451861 : ℝ)) := by rw [show ((-144076721435653136998814356451861/1446103041435653136998814356451861 : ℝ)) = -((144076721435653136998814356451861/1446103041435653136998814356451861 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnghi : Real.arctan ((-651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) = -Real.arctan ((651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) := by rw [show ((-651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) = -((651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : ((-1372189701441857997179/2000000000000000000000 : ℝ)) ≤ Real.arctan ((-651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) ∧ Real.arctan ((-651013160000000000000000000000000/795089881435653136998814356451861 : ℝ)) ≤ ((-686094850680928998587/1000000000000000000000 : ℝ)) := by
    rw [hnghi, hshhi, hfrhi, hgwhi]
    constructor <;> linarith [htwhi.1, htwhi.2, hp1, hp2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) = ((2048/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))) ≤ ((795089881435653136998814356451861/10000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) = deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 := by rw [h8]
  have htlo8 : ((-635770436/9765625 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8))) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8))) ≤ ((-16275329/250000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hminus) 2 2 (Real.sqrt 8))) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))) ≤ -((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))) < ((-635770436/9765625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3975368994487093386610055128668597/50000000000000000000000000000000 : ℝ)) < ((-635770436/9765625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t6 :
    ((101720469107867785339/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus) ∧ dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus) ≤ ((203451584727644819747/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((4/625 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 4 + ((-5000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((50964621070297370817944265294124377/7629394531250000000000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ≤ ((104387248352161481262939248774607/15625000000000000000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((50964621070297370817944265294124377/7629394531250000000000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ≤ ((104387248352161481262939248774607/15625000000000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f6
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((50964621070297370817944265294124377/7629394531250000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((104387248352161481262939248774607/15625000000000000000000000000 : ℝ)) ≤ ((8173606238704228414362387041466783/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus))) ≤ ((8173606238704228414362387041466783/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((404092827472641/8000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((154158886344391899/3051757812500000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((4/625 : ℝ)) ≤ ((4/625 : ℝ)) ∧ ((4/625 : ℝ)) ≤ ((4/625 : ℝ)) := by norm_num
    have hp1 : ((404092827472641/8000000000000 : ℝ)) ≤ ((4/625 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 4 + ((-5000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ∧ ((4/625 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 4 + ((-5000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ≤ ((154158886344391899/3051757812500000 : ℝ)) := by
      have hf := ztgcTrioF_f7
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-154158886344391899/3051757812500000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-404092827472641/8000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((154158886344391899/3051757812500000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-404092827472641/8000000000000 : ℝ)) < ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus))) ≤ -((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus))) < ((-154158886344391899/3051757812500000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) < ((-154158886344391899/3051757812500000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-404092827472641/8000000000000 : ℝ)) ≤ ((-1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ)) * ((8173606238704228414362387041466783/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus))) ≤ ((-1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-420956532311086145536000000000000/681095666153578124743338464150643 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-420956532311086145536000000000000/681095666153578124743338464150643 : ℝ)) * ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) ≤ ((-154158886344391899/3051757812500000 : ℝ)) := by norm_num
  have harg2 : ((-420956532311086145536000000000000/681095666153578124743338464150643 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((420956532311086145536000000000000/681095666153578124743338464150643 : ℝ))) (lo := ((6919895433452734573/12500000000000000000 : ℝ))) (hi := ((6919895433952734573/12500000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-420956532311086145536000000000000/681095666153578124743338464150643 : ℝ)) = -Real.arctan ((420956532311086145536000000000000/681095666153578124743338464150643 : ℝ)) := by rw [show ((-420956532311086145536000000000000/681095666153578124743338464150643 : ℝ)) = -((420956532311086145536000000000000/681095666153578124743338464150643 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((6919895433952734573/12500000000000000000 : ℝ)) ≤ Real.arctan ((-420956532311086145536000000000000/681095666153578124743338464150643 : ℝ)) ∧ Real.arctan ((-420956532311086145536000000000000/681095666153578124743338464150643 : ℝ)) ≤ -((6919895433452734573/12500000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ))) (lo := ((1107076808313345041/2000000000000000000 : ℝ))) (hi := ((1107076808393345041/2000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ)) = -Real.arctan ((1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ)) := by rw [show ((-1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ)) = -((1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((1107076808393345041/2000000000000000000 : ℝ)) ≤ Real.arctan ((-1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ)) ∧ Real.arctan ((-1683720114469337500000000000000000/2724535412901409471454129013822261 : ℝ)) ≤ -((1107076808313345041/2000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t7 :
    ((1560599470551627697/1562500000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2.52 2 2.52 (2 * hminus) ∧ dihY (2 * hminus) 2 2.52 2 2.52 (2 * hminus) ≤ ((199761138359758768247/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2.52 2 2.52 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)) = ((21752/625 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((164234716784918737688490539/24414062500000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ≤ ((4106132031300208106804559839/610351562500000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((164234716784918737688490539/24414062500000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ≤ ((4106132031300208106804559839/610351562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f8
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((164234716784918737688490539/24414062500000000000000 : ℝ)) := by norm_num
  have hs2 : ((4106132031300208106804559839/610351562500000000000000 : ℝ)) ≤ ((4101062886643655063328866436140527/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 (2 * hminus))) ≤ ((4101062886643655063328866436140527/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((66004619551/1250000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)) ≤ ((644586828871/12207031250 : ℝ)) := by
    rw [hE4]
    have hp0 : ((21752/625 : ℝ)) ≤ ((21752/625 : ℝ)) ∧ ((21752/625 : ℝ)) ≤ ((21752/625 : ℝ)) := by norm_num
    have hp1 : ((13396513/312500 : ℝ)) ≤ ((21752/625 : ℝ)) * (hminus) ∧ ((21752/625 : ℝ)) * (hminus) ≤ ((83728886/1953125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((66004619551/1250000000 : ℝ)) ≤ ((21752/625 : ℝ)) * (hminus) * (hminus) ∧ ((21752/625 : ℝ)) * (hminus) * (hminus) ≤ ((644586828871/12207031250 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp2.1, le_trans hp2.2 (by norm_num)⟩
  have htlo : ((-644586828871/12207031250 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)))) ≤ ((-66004619551/1250000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus))))| ≤ ((644586828871/12207031250 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-66004619551/1250000000 : ℝ)) < ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 (2 * hminus))) ≤ -((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 (2 * hminus))) < ((-644586828871/12207031250 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) < ((-644586828871/12207031250 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-66004619551/1250000000 : ℝ)) ≤ ((-2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ)) * ((4101062886643655063328866436140527/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 (2 * hminus))) ≤ ((-2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ)) * ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) ≤ ((-644586828871/12207031250 : ℝ)) := by norm_num
  have harg2 : ((-2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ))) (lo := ((11440253292037097863/20000000000000000000 : ℝ))) (hi := ((11440253292837097863/20000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ)) = -Real.arctan ((2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ)) := by rw [show ((-2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ)) = -((2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((11440253292837097863/20000000000000000000 : ℝ)) ≤ Real.arctan ((-2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ)) ∧ Real.arctan ((-2640227651055616000000000000000000/4100930991710948357590082890106331 : ℝ)) ≤ -((11440253292037097863/20000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ))) (lo := ((285995317998051389/500000000000000000 : ℝ))) (hi := ((285995318018051389/500000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ)) = -Real.arctan ((2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ)) := by rw [show ((-2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ)) = -((2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((285995318018051389/500000000000000000 : ℝ)) ≤ Real.arctan ((-2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ)) ∧ Real.arctan ((-2640184782040000000000000000000000/4101062886643655063328866436140527 : ℝ)) ≤ -((285995317998051389/500000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t8 :
    ((353727550941508231907/400000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8) ∧ dihY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8) ≤ ((176868680593933769287/200000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8) = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8) = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 = ((4/625 : ℝ)) * (((7500/1 : ℝ)) * hminus ^ 2 + ((-1031/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((19935100950657353410477333/3051757812500000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ≤ ((6379642737829547935022927/976562500000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((19935100950657353410477333/3051757812500000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ≤ ((6379642737829547935022927/976562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f9
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((19935100950657353410477333/3051757812500000000000 : ℝ)) := by norm_num
  have hs2 : ((6379642737829547935022927/976562500000000000000 : ℝ)) ≤ ((8082545492317125053354923170442279/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8))) ≤ ((8082545492317125053354923170442279/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((66227587/1000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 ∧ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 ≤ ((646765327/9765625 : ℝ)) := by
    rw [hE4]
    have hp0 : ((4/625 : ℝ)) ≤ ((4/625 : ℝ)) ∧ ((4/625 : ℝ)) ≤ ((4/625 : ℝ)) := by norm_num
    have hp1 : ((66227587/1000000 : ℝ)) ≤ ((4/625 : ℝ)) * (((7500/1 : ℝ)) * hminus ^ 2 + ((-1031/1 : ℝ))) ∧ ((4/625 : ℝ)) * (((7500/1 : ℝ)) * hminus ^ 2 + ((-1031/1 : ℝ))) ≤ ((646765327/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f10
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-646765327/9765625 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8)) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8)) ≤ ((-66227587/1000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8))| ≤ ((646765327/9765625 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-66227587/1000000 : ℝ)) < ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8))) ≤ -((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8))) < ((-646765327/9765625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) < ((-646765327/9765625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-66227587/1000000 : ℝ)) ≤ ((-6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) * ((8082545492317125053354923170442279/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8)) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8))) ≤ ((-6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) * ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) ≤ ((-646765327/9765625 : ℝ)) := by norm_num
  have harg2 : ((-6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8)) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have hshlo : Real.arctan ((6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) = Real.pi / 4 + Real.arctan (((((6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ))) - 1) / ((((6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrlo : (((((6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ))) - 1) / ((((6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ))) + 1)) = ((-1459408544814128198245067057909789/14705162441774128198245067057909789 : ℝ)) := by norm_num
  have htwlo := g4v_atan_pos_bounds (x := ((1459408544814128198245067057909789/14705162441774128198245067057909789 : ℝ))) (lo := ((19784142991264454031/200000000000000000000 : ℝ))) (hi := ((19784142999264454031/200000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwlo : Real.arctan ((-1459408544814128198245067057909789/14705162441774128198245067057909789 : ℝ)) = -Real.arctan ((1459408544814128198245067057909789/14705162441774128198245067057909789 : ℝ)) := by rw [show ((-1459408544814128198245067057909789/14705162441774128198245067057909789 : ℝ)) = -((1459408544814128198245067057909789/14705162441774128198245067057909789 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnglo : Real.arctan ((-6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) = -Real.arctan ((6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) := by rw [show ((-6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) = -((6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : ((-54918195875290083157/80000000000000000000 : ℝ)) ≤ Real.arctan ((-6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) ∧ Real.arctan ((-6622876948480000000000000000000000/8082285493294128198245067057909789 : ℝ)) ≤ ((-34323872420056301973/50000000000000000000 : ℝ)) := by
    rw [hnglo, hshlo, hfrlo, hgwlo]
    constructor <;> linarith [htwlo.1, htwlo.2, hp1, hp2]
  have hshhi : Real.arctan ((6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) = Real.pi / 4 + Real.arctan (((((6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ))) - 1) / ((((6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrhi : (((((6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ))) - 1) / ((((6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ))) + 1)) = ((-1459786792317125053354923170442279/14705304192317125053354923170442279 : ℝ)) := by norm_num
  have htwhi := g4v_atan_pos_bounds (x := ((1459786792317125053354923170442279/14705304192317125053354923170442279 : ℝ))) (lo := ((19789047706444107363/200000000000000000000 : ℝ))) (hi := ((19789047714444107363/200000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwhi : Real.arctan ((-1459786792317125053354923170442279/14705304192317125053354923170442279 : ℝ)) = -Real.arctan ((1459786792317125053354923170442279/14705304192317125053354923170442279 : ℝ)) := by rw [show ((-1459786792317125053354923170442279/14705304192317125053354923170442279 : ℝ)) = -((1459786792317125053354923170442279/14705304192317125053354923170442279 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnghi : Real.arctan ((-6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) = -Real.arctan ((6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) := by rw [show ((-6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) = -((6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : ((-274581169946091109121/400000000000000000000 : ℝ)) ≤ Real.arctan ((-6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) ∧ Real.arctan ((-6622758700000000000000000000000000/8082545492317125053354923170442279 : ℝ)) ≤ ((-214516539007883679/312500000000000000 : ℝ)) := by
    rw [hnghi, hshhi, hfrhi, hgwhi]
    constructor <;> linarith [htwhi.1, htwhi.2, hp1, hp2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))) ≤ ((8082545492317125053354923170442279/100000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) = deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) 8 := by rw [h8]
  have htlo8 : ((-646765327/9765625 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8))) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8))) ≤ ((-66227587/1000000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) 2 2 (Real.sqrt 8))) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))) ≤ -((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)))) < ((-646765327/9765625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) < ((-646765327/9765625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t9 :
    ((100416232887324064457/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus) ∧ dihY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus) ≤ ((8033715456123934279/8000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus) = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) = ((1/1562500 : ℝ)) * (((50000000/1 : ℝ)) * hminus ^ 4 + ((-50000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((53384367760921282624802224278499377/7629394531250000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((109343273396399010207884404051407/15625000000000000000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((53384367760921282624802224278499377/7629394531250000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((109343273396399010207884404051407/15625000000000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f11
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((53384367760921282624802224278499377/7629394531250000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((109343273396399010207884404051407/15625000000000000000000000000 : ℝ)) ≤ ((4182693359956499552233599564577253/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus))) ≤ ((4182693359956499552233599564577253/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((425735727952641/8000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) ≤ ((162414997672516899/3051757812500000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((1/1562500 : ℝ)) ≤ ((1/1562500 : ℝ)) ∧ ((1/1562500 : ℝ)) ≤ ((1/1562500 : ℝ)) := by norm_num
    have hp1 : ((425735727952641/8000000000000 : ℝ)) ≤ ((1/1562500 : ℝ)) * (((50000000/1 : ℝ)) * hminus ^ 4 + ((-50000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ∧ ((1/1562500 : ℝ)) * (((50000000/1 : ℝ)) * hminus ^ 4 + ((-50000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ≤ ((162414997672516899/3051757812500000 : ℝ)) := by
      have hf := ztgcTrioF_f12
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-162414997672516899/3051757812500000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)))) ≤ ((-425735727952641/8000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus))))| ≤ ((162414997672516899/3051757812500000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-425735727952641/8000000000000 : ℝ)) < ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus))) ≤ -((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus))) < ((-162414997672516899/3051757812500000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) < ((-162414997672516899/3051757812500000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-425735727952641/8000000000000 : ℝ)) ≤ ((-2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ)) * ((4182693359956499552233599564577253/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus))) ≤ ((-2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-443501220311086145536000000000000/697077024834939999196418317196967 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-443501220311086145536000000000000/697077024834939999196418317196967 : ℝ)) * ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) ≤ ((-162414997672516899/3051757812500000 : ℝ)) := by norm_num
  have harg2 : ((-443501220311086145536000000000000/697077024834939999196418317196967 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 (2 * hminus) (2 * hplus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((443501220311086145536000000000000/697077024834939999196418317196967 : ℝ))) (lo := ((28331699844082798733/50000000000000000000 : ℝ))) (hi := ((28331699846082798733/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-443501220311086145536000000000000/697077024834939999196418317196967 : ℝ)) = -Real.arctan ((443501220311086145536000000000000/697077024834939999196418317196967 : ℝ)) := by rw [show ((-443501220311086145536000000000000/697077024834939999196418317196967 : ℝ)) = -((443501220311086145536000000000000/697077024834939999196418317196967 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((28331699846082798733/50000000000000000000 : ℝ)) ≤ Real.arctan ((-443501220311086145536000000000000/697077024834939999196418317196967 : ℝ)) ∧ Real.arctan ((-443501220311086145536000000000000/697077024834939999196418317196967 : ℝ)) ≤ -((28331699844082798733/50000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ))) (lo := ((14164547394485120859/25000000000000000000 : ℝ))) (hi := ((14164547395485120859/25000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ)) = -Real.arctan ((2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ)) := by rw [show ((-2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ)) = -((2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((14164547395485120859/25000000000000000000 : ℝ)) ≤ Real.arctan ((-2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ)) ∧ Real.arctan ((-2660848299704006250000000000000000/4182693359956499552233599564577253 : ℝ)) ≤ -((14164547394485120859/25000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t10 :
    ((49353111673448186127/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus) ∧ dihY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus) ≤ ((197416804971844286413/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus) = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) = ((1/1562500 : ℝ)) * (((54380000/1 : ℝ)) * hminus ^ 2 + ((4227129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((344858720508567916296426703/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ≤ ((4311009344378920201883719391/610351562500000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((344858720508567916296426703/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ≤ ((4311009344378920201883719391/610351562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f13
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((344858720508567916296426703/48828125000000000000000 : ℝ)) := by norm_num
  have hs2 : ((4311009344378920201883719391/610351562500000000000000 : ℝ)) ≤ ((4202129730812271138997308122291177/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus))) ≤ ((4202129730812271138997308122291177/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((69386322751/1250000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) ≤ ((1355222548367/24414062500 : ℝ)) := by
    rw [hE4]
    have hp0 : ((1/1562500 : ℝ)) ≤ ((1/1562500 : ℝ)) ∧ ((1/1562500 : ℝ)) ≤ ((1/1562500 : ℝ)) := by norm_num
    have hp1 : ((69386322751/1250000000 : ℝ)) ≤ ((1/1562500 : ℝ)) * (((54380000/1 : ℝ)) * hminus ^ 2 + ((4227129/1 : ℝ))) ∧ ((1/1562500 : ℝ)) * (((54380000/1 : ℝ)) * hminus ^ 2 + ((4227129/1 : ℝ))) ≤ ((1355222548367/24414062500 : ℝ)) := by
      have hf := ztgcTrioF_f14
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-1355222548367/24414062500 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)))) ≤ ((-69386322751/1250000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus))))| ≤ ((1355222548367/24414062500 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-69386322751/1250000000 : ℝ)) < ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus))) ≤ -((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus))) < ((-1355222548367/24414062500 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) < ((-1355222548367/24414062500 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-95705272760000000000000000000000/144901025200423142724045107665213 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-69386322751/1250000000 : ℝ)) ≤ ((-95705272760000000000000000000000/144901025200423142724045107665213 : ℝ)) * ((4202129730812271138997308122291177/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus))) ≤ ((-95705272760000000000000000000000/144901025200423142724045107665213 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ)) * ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) ≤ ((-1355222548367/24414062500 : ℝ)) := by norm_num
  have harg2 : ((-2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 (2 * hminus) (2 * hplus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ))) (lo := ((58373409228593289669/100000000000000000000 : ℝ))) (hi := ((58373409232593289669/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ)) = -Real.arctan ((2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ)) := by rw [show ((-2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ)) = -((2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((58373409232593289669/100000000000000000000 : ℝ)) ≤ Real.arctan ((-2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ)) ∧ Real.arctan ((-2775495779055616000000000000000000/4201995536651404414344633485535657 : ℝ)) ≤ -((58373409228593289669/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((95705272760000000000000000000000/144901025200423142724045107665213 : ℝ))) (lo := ((58371230293567518717/100000000000000000000 : ℝ))) (hi := ((58371230297567518717/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-95705272760000000000000000000000/144901025200423142724045107665213 : ℝ)) = -Real.arctan ((95705272760000000000000000000000/144901025200423142724045107665213 : ℝ)) := by rw [show ((-95705272760000000000000000000000/144901025200423142724045107665213 : ℝ)) = -((95705272760000000000000000000000/144901025200423142724045107665213 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((58371230297567518717/100000000000000000000 : ℝ)) ≤ Real.arctan ((-95705272760000000000000000000000/144901025200423142724045107665213 : ℝ)) ∧ Real.arctan ((-95705272760000000000000000000000/144901025200423142724045107665213 : ℝ)) ≤ -((58371230293567518717/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t11 :
    ((70464590362796612027/80000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 ∧ dihY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 ≤ ((88083129906972659169/100000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) := by unfold deltaY; rw [h8]
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) = ((1/1562500 : ℝ)) * (((75000000/1 : ℝ)) * hminus ^ 2 + ((-6082871/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((340640702677430829037082953/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ≤ ((4258277604464001147492488927/610351562500000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((340640702677430829037082953/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ≤ ((4258277604464001147492488927/610351562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f15
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((340640702677430829037082953/48828125000000000000000 : ℝ)) := by norm_num
  have hs2 : ((4258277604464001147492488927/610351562500000000000000 : ℝ)) ≤ ((4176350687847573168406878475314049/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2)) ≤ ((4176350687847573168406878475314049/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((1723323739/25000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) ≤ ((2692739533/39062500 : ℝ)) := by
    rw [hE4]
    have hp0 : ((1/1562500 : ℝ)) ≤ ((1/1562500 : ℝ)) ∧ ((1/1562500 : ℝ)) ≤ ((1/1562500 : ℝ)) := by norm_num
    have hp1 : ((1723323739/25000000 : ℝ)) ≤ ((1/1562500 : ℝ)) * (((75000000/1 : ℝ)) * hminus ^ 2 + ((-6082871/1 : ℝ))) ∧ ((1/1562500 : ℝ)) * (((75000000/1 : ℝ)) * hminus ^ 2 + ((-6082871/1 : ℝ))) ≤ ((2692739533/39062500 : ℝ)) := by
      have hf := ztgcTrioF_f16
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-2692739533/39062500 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2))) ≤ ((-1723323739/25000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2)))| ≤ ((2692739533/39062500 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-1723323739/25000000 : ℝ)) < ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2)) ≤ -((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2)) < ((-2692739533/39062500 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) < ((-2692739533/39062500 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-1723323739/25000000 : ℝ)) ≤ ((-3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) * ((4176350687847573168406878475314049/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2)) ≤ ((-3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) * ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) ≤ ((-2692739533/39062500 : ℝ)) := by norm_num
  have harg2 : ((-626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have hshlo : Real.arctan ((626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) = Real.pi / 4 + Real.arctan (((((626673927680000000000000000000000/759312520227792181047524994729531 : ℝ))) - 1) / ((((626673927680000000000000000000000/759312520227792181047524994729531 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrlo : (((((626673927680000000000000000000000/759312520227792181047524994729531 : ℝ))) - 1) / ((((626673927680000000000000000000000/759312520227792181047524994729531 : ℝ))) + 1)) = ((-132638592547792181047524994729531/1385986447907792181047524994729531 : ℝ)) := by norm_num
  have htwlo := g4v_atan_pos_bounds (x := ((132638592547792181047524994729531/1385986447907792181047524994729531 : ℝ))) (lo := ((3816368685500373629/40000000000000000000 : ℝ))) (hi := ((3816368687100373629/40000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwlo : Real.arctan ((-132638592547792181047524994729531/1385986447907792181047524994729531 : ℝ)) = -Real.arctan ((132638592547792181047524994729531/1385986447907792181047524994729531 : ℝ)) := by rw [show ((-132638592547792181047524994729531/1385986447907792181047524994729531 : ℝ)) = -((132638592547792181047524994729531/1385986447907792181047524994729531 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnglo : Real.arctan ((-626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) = -Real.arctan ((626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) := by rw [show ((-626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) = -((626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : ((-275995578503975587557/400000000000000000000 : ℝ)) ≤ Real.arctan ((-626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) ∧ Real.arctan ((-626673927680000000000000000000000/759312520227792181047524994729531 : ℝ)) ≤ ((-68998894621993896889/100000000000000000000 : ℝ)) := by
    rw [hnglo, hshlo, hfrlo, hgwlo]
    constructor <;> linarith [htwlo.1, htwlo.2, hp1, hp2]
  have hshhi : Real.arctan ((3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) = Real.pi / 4 + Real.arctan (((((3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ))) - 1) / ((((3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrhi : (((((3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ))) - 1) / ((((3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ))) + 1)) = ((-729703209847573168406878475314049/7622998165847573168406878475314049 : ℝ)) := by norm_num
  have htwhi := g4v_atan_pos_bounds (x := ((729703209847573168406878475314049/7622998165847573168406878475314049 : ℝ))) (lo := ((9543313463227828207/100000000000000000000 : ℝ))) (hi := ((9543313467227828207/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwhi : Real.arctan ((-729703209847573168406878475314049/7622998165847573168406878475314049 : ℝ)) = -Real.arctan ((729703209847573168406878475314049/7622998165847573168406878475314049 : ℝ)) := by rw [show ((-729703209847573168406878475314049/7622998165847573168406878475314049 : ℝ)) = -((729703209847573168406878475314049/7622998165847573168406878475314049 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnghi : Real.arctan ((-3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) = -Real.arctan ((3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) := by rw [show ((-3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) = -((3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : ((-275986011506068011019/400000000000000000000 : ℝ)) ≤ Real.arctan ((-3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) ∧ Real.arctan ((-3446647478000000000000000000000000/4176350687847573168406878475314049 : ℝ)) ≤ ((-137993005745034005509/200000000000000000000 : ℝ)) := by
    rw [hnghi, hshhi, hfrhi, hgwhi]
    constructor <;> linarith [htwhi.1, htwhi.2, hp1, hp2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ≤ ((4176350687847573168406878475314049/50000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) := by rw [h8]
  have htlo8 : ((-2692739533/39062500 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2)) ≤ ((-1723323739/25000000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2 (Real.sqrt 8) 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ≤ -((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) < ((-2692739533/39062500 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) < ((-2692739533/39062500 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t12 :
    ((142667648870347128903/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((285338561812078116401/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp5.1, le_trans hp5.2 (by norm_num)⟩
  have hs1 : ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((4975811493065949357729530623663/762939453125000000000000000 : ℝ)) := by norm_num
  have hs2 : ((39810277905406602174508717528079/6103515625000000000000000000 : ℝ)) ≤ ((2019052366213842803823662138226133/25000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) ≤ ((2019052366213842803823662138226133/25000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((1831146108781639/156250000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1831146108781639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-2/1 : ℝ))) ≤ ((1831269284281639/156250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f17
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-1831269284281639/156250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-1831146108781639/156250000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((1831269284281639/156250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-1831146108781639/156250000000000 : ℝ)) < ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) ≤ -((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) < ((-1831269284281639/156250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) < ((-1831269284281639/156250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-1831146108781639/156250000000000 : ℝ)) ≤ ((-292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ)) * ((2019052366213842803823662138226133/25000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) ≤ ((-292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ)) * ((8075825431614573170645683853460711/100000000000000000000000000000000 : ℝ)) ≤ ((-1831269284281639/156250000000000 : ℝ)) := by norm_num
  have harg2 : ((-1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ))) (lo := ((720599185257126651/5000000000000000000 : ℝ))) (hi := ((720599185457126651/5000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ)) = -Real.arctan ((1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ)) := by rw [show ((-1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ)) = -((1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((720599185457126651/5000000000000000000 : ℝ)) ≤ Real.arctan ((-1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ)) ∧ Real.arctan ((-1172012341940248960000000000000000/8075825431614573170645683853460711 : ℝ)) ≤ -((720599185257126651/5000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ))) (lo := ((14410351873450603723/100000000000000000000 : ℝ))) (hi := ((14410351877450603723/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ)) = -Real.arctan ((292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ)) := by rw [show ((-292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ)) = -((292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((14410351877450603723/100000000000000000000 : ℝ)) ≤ Real.arctan ((-292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ)) ∧ Real.arctan ((-292983377405062240000000000000000/2019052366213842803823662138226133 : ℝ)) ≤ -((14410351873450603723/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t13 :
    ((1582746046800520155037/1000000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ∧ dihY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) ≤ ((395690978235464162663/250000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((5420357059985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((2710353909271079/2441406250000 : ℝ)) := by
      have hf := ztgcTrioF_f18
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((218306663888374772190337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((1066029919138303725130111/381469726562500000000 : ℝ)) := by
      have hf := ztgcTrioF_f19
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f20
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp5.1, le_trans hp5.2 (by norm_num)⟩
  have hs1 : ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) ≤ ((1747787643417565377776434175478999/25000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus))) ≤ ((1747787643417565377776434175478999/25000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-638330377601881/762939453125000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-638330377601881/762939453125000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (((2/1 : ℝ)) * hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((-6683702058241/8000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f21
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((6683702058241/8000000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((638330377601881/762939453125000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((638330377601881/762939453125000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((638330377601881/762939453125000 : ℝ)) < ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus))) ≤ -((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus))) < ((6683702058241/8000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) < ((6683702058241/8000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((638330377601881/762939453125000 : ℝ)) := by norm_num
  have hnum : ((638330377601881/762939453125000 : ℝ)) ≤ ((83667239253033746432000000000000/6990820952352127489890476478026019 : ℝ)) * ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus))) ≤ ((83667239253033746432000000000000/6990820952352127489890476478026019 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((20886568932003125000000000000000/1747787643417565377776434175478999 : ℝ)) := by norm_num
  have hnum2 : ((20886568932003125000000000000000/1747787643417565377776434175478999 : ℝ)) * ((1747787643417565377776434175478999/25000000000000000000000000000000 : ℝ)) ≤ ((6683702058241/8000000000000 : ℝ)) := by norm_num
  have harg2 : ((20886568932003125000000000000000/1747787643417565377776434175478999 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((20886568932003125000000000000000/1747787643417565377776434175478999 : ℝ))) (lo := ((11949721005623535807/1000000000000000000000 : ℝ))) (hi := ((11949721045623535807/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((83667239253033746432000000000000/6990820952352127489890476478026019 : ℝ))) (lo := ((11967585106960031417/1000000000000000000000 : ℝ))) (hi := ((11967585146960031417/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t14 :
    ((203958058195539470957/125000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2.52 2 2 ∧ dihY (2 * hminus) 2 (2 * hminus) 2.52 2 2 ≤ ((163166768270202825141/100000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 (2 * hminus) 2.52 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) = ((-1752/625 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((118892084664640922922865539/24414062500000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ≤ ((2972520368903210204693839839/610351562500000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((118892084664640922922865539/24414062500000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ≤ ((2972520368903210204693839839/610351562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f22
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((118892084664640922922865539/24414062500000000000000 : ℝ)) := by norm_num
  have hs2 : ((2972520368903210204693839839/610351562500000000000000 : ℝ)) ≤ ((872333201499998526632014999898033/12500000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2.52 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2.52 2 2)) ≤ ((872333201499998526632014999898033/12500000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-51917806371/12207031250 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) ≤ ((-5316297051/1250000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1752/625 : ℝ)) ≤ ((-1752/625 : ℝ)) ∧ ((-1752/625 : ℝ)) ≤ ((-1752/625 : ℝ)) := by norm_num
    have hp1 : ((-6743886/1953125 : ℝ)) ≤ ((-1752/625 : ℝ)) * (hminus) ∧ ((-1752/625 : ℝ)) * (hminus) ≤ ((-1079013/312500 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-51917806371/12207031250 : ℝ)) ≤ ((-1752/625 : ℝ)) * (hminus) * (hminus) ∧ ((-1752/625 : ℝ)) * (hminus) * (hminus) ≤ ((-5316297051/1250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp2.1, le_trans hp2.2 (by norm_num)⟩
  have htlo : ((5316297051/1250000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2))) ≤ ((51917806371/12207031250 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2)))| ≤ ((51917806371/12207031250 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((51917806371/12207031250 : ℝ)) < ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2.52 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2.52 2 2)) ≤ -((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2.52 2 2)) < ((5316297051/1250000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) < ((5316297051/1250000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2.52 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((51917806371/12207031250 : ℝ)) := by norm_num
  have hnum : ((51917806371/12207031250 : ℝ)) ≤ ((141770223263744000000000000000000/2326136469643170834535303568059041 : ℝ)) * ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2.52 2 2)) ≤ ((141770223263744000000000000000000/2326136469643170834535303568059041 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((53162970510000000000000000000000/872333201499998526632014999898033 : ℝ)) := by norm_num
  have hnum2 : ((53162970510000000000000000000000/872333201499998526632014999898033 : ℝ)) * ((872333201499998526632014999898033/12500000000000000000000000000000 : ℝ)) ≤ ((5316297051/1250000000 : ℝ)) := by norm_num
  have harg2 : ((53162970510000000000000000000000/872333201499998526632014999898033 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2.52 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((53162970510000000000000000000000/872333201499998526632014999898033 : ℝ))) (lo := ((30434069884709574213/500000000000000000000 : ℝ))) (hi := ((30434069904709574213/500000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((141770223263744000000000000000000/2326136469643170834535303568059041 : ℝ))) (lo := ((2434854194685265287/40000000000000000000 : ℝ))) (hi := ((2434854196285265287/40000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t15 :
    ((96269378049951433557/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2 ∧ dihY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2 ≤ ((15403245521702652127/8000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ)) := by norm_num
  have hs2 : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2)) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-237067609/9765625 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) ≤ ((-24275329/1000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp2.1, le_trans hp2.2 (by norm_num)⟩
  have htlo : ((24275329/1000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2))) ≤ ((237067609/9765625 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2)))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((237067609/9765625 : ℝ)) < ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2)) ≤ -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2)) < ((24275329/1000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) < ((24275329/1000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((237067609/9765625 : ℝ)) := by norm_num
  have hnum : ((237067609/9765625 : ℝ)) ≤ ((2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) * ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2)) ≤ ((2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) := by norm_num
  have hnum2 : ((2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) * ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) ≤ ((24275329/1000000 : ℝ)) := by norm_num
  have harg2 : ((2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ))) (lo := ((35459123520413205191/100000000000000000000 : ℝ))) (hi := ((35459123524413205191/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ))) (lo := ((138519282178880819/390625000000000000 : ℝ))) (hi := ((138519282194505819/390625000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) := by rw [h8]
  have htlo8 : ((24275329/1000000 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) ≤ ((237067609/9765625 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 (Real.sqrt 8) 2 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) < ((24275329/1000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) < ((24275329/1000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t16 :
    ((55126375427410257267/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ∧ dihY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) ≤ ((220510748838481597491/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((3314273926065743134310829686999/625000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((316094440315200000133914599787959/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-58402079612368/30517578125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/62500000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-224804204947907524/95367431640625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((-865327585895733036757/298023223876953125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-2903439703632953407/1000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    have hp6 : ((-13323448840036601566947529/3725290298461914062500 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-14305247419799561436289/4000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp5.1, hp5.2, hf.1, hf.2]
    have hp7 : ((3314273926065743134310829686999/625000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((316094440315200000133914599787959/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f23
      constructor <;> nlinarith [hp6.1, hp6.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp7.1, le_trans hp7.2 (by norm_num)⟩
  have hs1 : ((3641029484124333123805158756304659/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((3314273926065743134310829686999/625000000000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((316094440315200000133914599787959/59604644775390625000000000000 : ℝ)) ≤ ((7282296822821303092868228212302699/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((3641029484124333123805158756304659/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus))) ≤ ((7282296822821303092868228212302699/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((589291598058241/16000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((119604545983/4000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((3650129975773/122070312500 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((589291598058241/16000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp4.1, le_trans hp4.2 (by norm_num)⟩
  have htlo : ((-56201051236976881/1525878906250000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-589291598058241/16000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((56201051236976881/1525878906250000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-589291598058241/16000000000000 : ℝ)) < ((3641029484124333123805158756304659/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((3641029484124333123805158756304659/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus))) ≤ -((3641029484124333123805158756304659/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus))) < ((-56201051236976881/1525878906250000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3641029484124333123805158756304659/50000000000000000000000000000000 : ℝ)) < ((-56201051236976881/1525878906250000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-589291598058241/16000000000000 : ℝ)) ≤ ((-3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ)) * ((7282296822821303092868228212302699/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus))) ≤ ((-3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ)) * ((3641029484124333123805158756304659/50000000000000000000000000000000 : ℝ)) ≤ ((-56201051236976881/1525878906250000 : ℝ)) := by norm_num
  have harg2 : ((-1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ))) (lo := ((46826881720669147389/100000000000000000000 : ℝ))) (hi := ((46826881724669147389/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ)) = -Real.arctan ((1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ)) := by rw [show ((-1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ)) = -((1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((46826881724669147389/100000000000000000000 : ℝ)) ≤ Real.arctan ((-1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ)) ∧ Real.arctan ((-1841596046933258436608000000000000/3641029484124333123805158756304659 : ℝ)) ≤ -((46826881720669147389/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ))) (lo := ((23412129180124431589/50000000000000000000 : ℝ))) (hi := ((23412129182124431589/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ)) = -Real.arctan ((3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ)) := by rw [show ((-3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ)) = -((3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((23412129182124431589/50000000000000000000 : ℝ)) ≤ Real.arctan ((-3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ)) ∧ Real.arctan ((-3683072487864006250000000000000000/7282296822821303092868228212302699 : ℝ)) ≤ -((23412129180124431589/50000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t17 :
    ((21736395041515063001/20000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2.52 2 2 2 (2 * hminus) ∧ dihY (2 * hminus) 2.52 2 2 2 (2 * hminus) ≤ ((43473846397086847289/40000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2.52 2 2 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((15876/625 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-15876/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-254016/390625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((640767964053867341669356743/119209289550781250000000 : ℝ)) ≤ ((-254016/390625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ∧ ((-254016/390625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ≤ ((524967381677133246251443239/97656250000000000000000 : ℝ)) := by
    have hp0 : ((-254016/390625 : ℝ)) ≤ ((-254016/390625 : ℝ)) ∧ ((-254016/390625 : ℝ)) ≤ ((-254016/390625 : ℝ)) := by norm_num
    have hp1 : ((-977771088/1220703125 : ℝ)) ≤ ((-254016/390625 : ℝ)) * (hminus) ∧ ((-254016/390625 : ℝ)) * (hminus) ≤ ((-39110526/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-3763685360484/3814697265625 : ℝ)) ≤ ((-254016/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-254016/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-96348780801/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((640767964053867341669356743/119209289550781250000000 : ℝ)) ≤ ((-254016/390625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ∧ ((-254016/390625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ≤ ((524967381677133246251443239/97656250000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f24
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((366577115673014854328843269814799/5000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((640767964053867341669356743/119209289550781250000000 : ℝ)) := by norm_num
  have hs2 : ((524967381677133246251443239/97656250000000000000000 : ℝ)) ≤ ((916486666942531135566669425219707/12500000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((366577115673014854328843269814799/5000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 2 (2 * hminus))) ≤ ((916486666942531135566669425219707/12500000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((96348780801/2500000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((940921340121/24414062500 : ℝ)) := by
    rw [hE4]
    have hp0 : ((15876/625 : ℝ)) ≤ ((15876/625 : ℝ)) ∧ ((15876/625 : ℝ)) ≤ ((15876/625 : ℝ)) := by norm_num
    have hp1 : ((19555263/625000 : ℝ)) ≤ ((15876/625 : ℝ)) * (hminus) ∧ ((15876/625 : ℝ)) * (hminus) ≤ ((61110693/1953125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((96348780801/2500000000 : ℝ)) ≤ ((15876/625 : ℝ)) * (hminus) * (hminus) ∧ ((15876/625 : ℝ)) * (hminus) * (hminus) ≤ ((940921340121/24414062500 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp2.1, le_trans hp2.2 (by norm_num)⟩
  have htlo : ((-940921340121/24414062500 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-96348780801/2500000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((940921340121/24414062500 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-96348780801/2500000000 : ℝ)) < ((366577115673014854328843269814799/5000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((366577115673014854328843269814799/5000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 2 (2 * hminus))) ≤ -((366577115673014854328843269814799/5000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 2 (2 * hminus))) < ((-940921340121/24414062500 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((366577115673014854328843269814799/5000000000000000000000000000000 : ℝ)) < ((-940921340121/24414062500 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-481743904005000000000000000000000/916486666942531135566669425219707 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-96348780801/2500000000 : ℝ)) ≤ ((-481743904005000000000000000000000/916486666942531135566669425219707 : ℝ)) * ((916486666942531135566669425219707/12500000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 2 (2 * hminus))) ≤ ((-481743904005000000000000000000000/916486666942531135566669425219707 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-21411187828531200000000000000000/40730790630334983814315918868311 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-21411187828531200000000000000000/40730790630334983814315918868311 : ℝ)) * ((366577115673014854328843269814799/5000000000000000000000000000000 : ℝ)) ≤ ((-940921340121/24414062500 : ℝ)) := by norm_num
  have harg2 : ((-21411187828531200000000000000000/40730790630334983814315918868311 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 2 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((21411187828531200000000000000000/40730790630334983814315918868311 : ℝ))) (lo := ((24198828683957173459/50000000000000000000 : ℝ))) (hi := ((24198828685957173459/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-21411187828531200000000000000000/40730790630334983814315918868311 : ℝ)) = -Real.arctan ((21411187828531200000000000000000/40730790630334983814315918868311 : ℝ)) := by rw [show ((-21411187828531200000000000000000/40730790630334983814315918868311 : ℝ)) = -((21411187828531200000000000000000/40730790630334983814315918868311 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((24198828685957173459/50000000000000000000 : ℝ)) ≤ Real.arctan ((-21411187828531200000000000000000/40730790630334983814315918868311 : ℝ)) ∧ Real.arctan ((-21411187828531200000000000000000/40730790630334983814315918868311 : ℝ)) ≤ -((24198828683957173459/50000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((481743904005000000000000000000000/916486666942531135566669425219707 : ℝ))) (lo := ((48395016786772543701/100000000000000000000 : ℝ))) (hi := ((48395016790772543701/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-481743904005000000000000000000000/916486666942531135566669425219707 : ℝ)) = -Real.arctan ((481743904005000000000000000000000/916486666942531135566669425219707 : ℝ)) := by rw [show ((-481743904005000000000000000000000/916486666942531135566669425219707 : ℝ)) = -((481743904005000000000000000000000/916486666942531135566669425219707 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((48395016790772543701/100000000000000000000 : ℝ)) ≤ Real.arctan ((-481743904005000000000000000000000/916486666942531135566669425219707 : ℝ)) ∧ Real.arctan ((-481743904005000000000000000000000/916486666942531135566669425219707 : ℝ)) ≤ -((48395016786772543701/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t18 :
    ((104840038191742998781/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) ∧ dihY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) ≤ ((209685910628107188469/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((43917129/1562500 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-43917129/9765625000000 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-43917129/610351562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((13080008660866889667555912065901/2384185791015625000000000000 : ℝ)) ≤ ((-43917129/610351562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ∧ ((-43917129/610351562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ≤ ((5358120419991341345638142519199/976562500000000000000000000 : ℝ)) := by
    have hp0 : ((-43917129/610351562500 : ℝ)) ≤ ((-43917129/610351562500 : ℝ)) ∧ ((-43917129/610351562500 : ℝ)) ≤ ((-43917129/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-676192035213/7629394531250000 : ℝ)) ≤ ((-43917129/610351562500 : ℝ)) * (hminus) ∧ ((-43917129/610351562500 : ℝ)) * (hminus) ≤ ((-216379694583/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-10411328766174561/95367431640625000000 : ℝ)) ≤ ((-43917129/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-43917129/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-1066102755210441/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((13080008660866889667555912065901/2384185791015625000000000000 : ℝ)) ≤ ((-43917129/610351562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ∧ ((-43917129/610351562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 4 + ((-100000000/1 : ℝ)) * hminus ^ 2 + ((43917129/1 : ℝ))) ≤ ((5358120419991341345638142519199/976562500000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f25
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((7406857136890621948728631093039827/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((13080008660866889667555912065901/2384185791015625000000000000 : ℝ)) := by norm_num
  have hs2 : ((5358120419991341345638142519199/976562500000000000000000000 : ℝ)) ≤ ((7407236536030993571265360309194989/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((7406857136890621948728631093039827/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus))) ≤ ((7407236536030993571265360309194989/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((1066102755210441/25000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((10411328766174561/244140625000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((43917129/1562500 : ℝ)) ≤ ((43917129/1562500 : ℝ)) ∧ ((43917129/1562500 : ℝ)) ≤ ((43917129/1562500 : ℝ)) := by norm_num
    have hp1 : ((216379694583/6250000000 : ℝ)) ≤ ((43917129/1562500 : ℝ)) * (hminus) ∧ ((43917129/1562500 : ℝ)) * (hminus) ≤ ((676192035213/19531250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((1066102755210441/25000000000000 : ℝ)) ≤ ((43917129/1562500 : ℝ)) * (hminus) * (hminus) ∧ ((43917129/1562500 : ℝ)) * (hminus) * (hminus) ≤ ((10411328766174561/244140625000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp2.1, le_trans hp2.2 (by norm_num)⟩
  have htlo : ((-10411328766174561/244140625000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-1066102755210441/25000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((10411328766174561/244140625000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-1066102755210441/25000000000000 : ℝ)) < ((7406857136890621948728631093039827/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((7406857136890621948728631093039827/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus))) ≤ -((7406857136890621948728631093039827/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus))) < ((-10411328766174561/244140625000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((7406857136890621948728631093039827/100000000000000000000000000000000 : ℝ)) < ((-10411328766174561/244140625000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-1066102755210441/25000000000000 : ℝ)) ≤ ((-4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ)) * ((7407236536030993571265360309194989/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus))) ≤ ((-4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-473831140291677798400000000000000/822984126321180216525403454782203 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-473831140291677798400000000000000/822984126321180216525403454782203 : ℝ)) * ((7406857136890621948728631093039827/100000000000000000000000000000000 : ℝ)) ≤ ((-10411328766174561/244140625000000 : ℝ)) := by norm_num
  have harg2 : ((-473831140291677798400000000000000/822984126321180216525403454782203 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((473831140291677798400000000000000/822984126321180216525403454782203 : ℝ))) (lo := ((26119797191873331571/50000000000000000000 : ℝ))) (hi := ((26119797193873331571/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-473831140291677798400000000000000/822984126321180216525403454782203 : ℝ)) = -Real.arctan ((473831140291677798400000000000000/822984126321180216525403454782203 : ℝ)) := by rw [show ((-473831140291677798400000000000000/822984126321180216525403454782203 : ℝ)) = -((473831140291677798400000000000000/822984126321180216525403454782203 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((26119797193873331571/50000000000000000000 : ℝ)) ≤ Real.arctan ((-473831140291677798400000000000000/822984126321180216525403454782203 : ℝ)) ∧ Real.arctan ((-473831140291677798400000000000000/822984126321180216525403454782203 : ℝ)) ≤ -((26119797191873331571/50000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ))) (lo := ((52236677465436067689/100000000000000000000 : ℝ))) (hi := ((52236677469436067689/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ)) = -Real.arctan ((4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ)) := by rw [show ((-4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ)) = -((4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((52236677469436067689/100000000000000000000 : ℝ)) ≤ Real.arctan ((-4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ)) ∧ Real.arctan ((-4264411020841764000000000000000000/7407236536030993571265360309194989 : ℝ)) ≤ -((52236677465436067689/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t19 :
    ((49536471084505416149/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2 ∧ dihY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2 ≤ ((198152613812277251327/200000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) = ((32/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) = ((-128/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) = ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((130891583584762231480847/23841857910156250000 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((107238643423195450705831/19531250000000000000 : ℝ)) := by
    have hp0 : ((-2048/1 : ℝ)) ≤ ((-2048/1 : ℝ)) ∧ ((-2048/1 : ℝ)) ≤ ((-2048/1 : ℝ)) := by norm_num
    have hp1 : ((-7883264/3125 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) ≤ ((-315328/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-30344653952/9765625 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) ≤ ((-48550658/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((130891583584762231480847/23841857910156250000 : ℝ)) ≤ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ∧ ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) ≤ ((107238643423195450705831/19531250000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f26
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((130891583584762231480847/23841857910156250000 : ℝ)) := by norm_num
  have hs2 : ((107238643423195450705831/19531250000000000000 : ℝ)) ≤ ((185246770269884140167702698822877/2500000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2)) ≤ ((185246770269884140167702698822877/2500000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((24275329/500000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) ≤ ((474135218/9765625 : ℝ)) := by
    rw [hE4]
    have hp0 : ((32/1 : ℝ)) ≤ ((32/1 : ℝ)) ∧ ((32/1 : ℝ)) ≤ ((32/1 : ℝ)) := by norm_num
    have hp1 : ((4927/125 : ℝ)) ≤ ((32/1 : ℝ)) * (hminus) ∧ ((32/1 : ℝ)) * (hminus) ≤ ((123176/3125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/500000 : ℝ)) ≤ ((32/1 : ℝ)) * (hminus) * (hminus) ∧ ((32/1 : ℝ)) * (hminus) * (hminus) ≤ ((474135218/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp2.1, le_trans hp2.2 (by norm_num)⟩
  have htlo : ((-474135218/9765625 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2))) ≤ ((-24275329/500000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2)))| ≤ ((474135218/9765625 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-24275329/500000 : ℝ)) < ((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2)) ≤ -((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2)) < ((-474135218/9765625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) < ((-474135218/9765625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-121376645000000000000000000000000/185246770269884140167702698822877 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-24275329/500000 : ℝ)) ≤ ((-121376645000000000000000000000000/185246770269884140167702698822877 : ℝ)) * ((185246770269884140167702698822877/2500000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2)) ≤ ((-121376645000000000000000000000000/185246770269884140167702698822877 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ)) * ((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) ≤ ((-474135218/9765625 : ℝ)) := by norm_num
  have harg2 : ((-971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ))) (lo := ((464053523251830637/800000000000000000 : ℝ))) (hi := ((464053523283830637/800000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ)) = -Real.arctan ((971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ)) := by rw [show ((-971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ)) = -((971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((464053523283830637/800000000000000000 : ℝ)) ≤ Real.arctan ((-971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ)) ∧ Real.arctan ((-971028926464000000000000000000000/1481889459569628744805404303564363 : ℝ)) ≤ -((464053523251830637/800000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((121376645000000000000000000000000/185246770269884140167702698822877 : ℝ))) (lo := ((2900166293667551813/5000000000000000000 : ℝ))) (hi := ((2900166293867551813/5000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-121376645000000000000000000000000/185246770269884140167702698822877 : ℝ)) = -Real.arctan ((121376645000000000000000000000000/185246770269884140167702698822877 : ℝ)) := by rw [show ((-121376645000000000000000000000000/185246770269884140167702698822877 : ℝ)) = -((121376645000000000000000000000000/185246770269884140167702698822877 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((2900166293867551813/5000000000000000000 : ℝ)) ≤ Real.arctan ((-121376645000000000000000000000000/185246770269884140167702698822877 : ℝ)) ∧ Real.arctan ((-121376645000000000000000000000000/185246770269884140167702698822877 : ℝ)) ≤ -((2900166293667551813/5000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) = ((-2048/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((2/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ≤ ((185246770269884140167702698822877/2500000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) := by rw [h8]
  have htlo8 : ((-474135218/9765625 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2)) ≤ ((-24275329/500000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 (Real.sqrt 8) 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ≤ -((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) < ((-474135218/9765625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((1481889459569628744805404303564363/20000000000000000000000000000000 : ℝ)) < ((-474135218/9765625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t20 :
    ((121618696337696172259/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 2 2 (2 * hminus) ∧ dihY (2 * hminus) 2 2 2 2 (2 * hminus) ≤ ((48648203703630582693/40000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2 2 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((16/1 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ)) := by norm_num
  have hs2 : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus))) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((24275329/1000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((237067609/9765625 : ℝ)) := by
    rw [hE4]
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by norm_num
    have hp1 : ((4927/250 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) ≤ ((61588/3125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((24275329/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (hminus) * (hminus) ∧ ((16/1 : ℝ)) * (hminus) * (hminus) ≤ ((237067609/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp2.1, le_trans hp2.2 (by norm_num)⟩
  have htlo : ((-237067609/9765625 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-24275329/1000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((237067609/9765625 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-24275329/1000000 : ℝ)) < ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus))) ≤ -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus))) < ((-237067609/9765625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) < ((-237067609/9765625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-24275329/1000000 : ℝ)) ≤ ((-2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) * ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus))) ≤ ((-2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) * ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ ((-237067609/9765625 : ℝ)) := by norm_num
  have harg2 : ((-2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ))) (lo := ((138519282178880819/390625000000000000 : ℝ))) (hi := ((138519282194505819/390625000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) = -Real.arctan ((2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) := by rw [show ((-2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) = -((2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((138519282194505819/390625000000000000 : ℝ)) ≤ Real.arctan ((-2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) ∧ Real.arctan ((-2427572316160000000000000000000000/6556383545049379476864549505549593 : ℝ)) ≤ -((138519282178880819/390625000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ))) (lo := ((35459123520413205191/100000000000000000000 : ℝ))) (hi := ((35459123524413205191/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) = -Real.arctan ((2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) := by rw [show ((-2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) = -((2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((35459123524413205191/100000000000000000000 : ℝ)) ≤ Real.arctan ((-2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) ∧ Real.arctan ((-2427532900000000000000000000000000/6556642093309874663320933098090969 : ℝ)) ≤ -((35459123520413205191/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t21 :
    ((14663549735043208201/10000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2 ∧ dihY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2 ≤ ((293280809380584634023/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-4/625 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 4 + ((-7500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((50964621070297370817944265294124377/7629394531250000000000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ≤ ((104387248352161481262939248774607/15625000000000000000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((50964621070297370817944265294124377/7629394531250000000000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ≤ ((104387248352161481262939248774607/15625000000000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f6
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((50964621070297370817944265294124377/7629394531250000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((104387248352161481262939248774607/15625000000000000000000000000 : ℝ)) ≤ ((8173606238704228414362387041466783/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2)) ≤ ((8173606238704228414362387041466783/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((52268952164731827/6103515625000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) ≤ ((68538557820159/8000000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) ∧ ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) := by norm_num
    have hp1 : ((52268952164731827/6103515625000000 : ℝ)) ≤ ((-4/625 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 4 + ((-7500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ∧ ((-4/625 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 4 + ((-7500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ≤ ((68538557820159/8000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f27
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-68538557820159/8000000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) ≤ ((-52268952164731827/6103515625000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2)))| ≤ ((68538557820159/8000000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-52268952164731827/6103515625000000 : ℝ)) < ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2)) ≤ -((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2)) < ((-68538557820159/8000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) < ((-68538557820159/8000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-52268952164731827/6103515625000000 : ℝ)) ≤ ((-285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ)) * ((8173606238704228414362387041466783/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2)) ≤ ((-285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-23798110354221875000000000000000/227031888717859374914446154716881 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-23798110354221875000000000000000/227031888717859374914446154716881 : ℝ)) * ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) ≤ ((-68538557820159/8000000000000 : ℝ)) := by norm_num
  have harg2 : ((-23798110354221875000000000000000/227031888717859374914446154716881 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 (2 * hminus) (2 * hminus) 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((23798110354221875000000000000000/227031888717859374914446154716881 : ℝ))) (lo := ((10444135225057579913/100000000000000000000 : ℝ))) (hi := ((10444135229057579913/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-23798110354221875000000000000000/227031888717859374914446154716881 : ℝ)) = -Real.arctan ((23798110354221875000000000000000/227031888717859374914446154716881 : ℝ)) := by rw [show ((-23798110354221875000000000000000/227031888717859374914446154716881 : ℝ)) = -((23798110354221875000000000000000/227031888717859374914446154716881 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((10444135229057579913/100000000000000000000 : ℝ)) ≤ Real.arctan ((-23798110354221875000000000000000/227031888717859374914446154716881 : ℝ)) ∧ Real.arctan ((-23798110354221875000000000000000/227031888717859374914446154716881 : ℝ)) ≤ -((10444135225057579913/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ))) (lo := ((652451755574834057/6250000000000000000 : ℝ))) (hi := ((652451755824834057/6250000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ)) = -Real.arctan ((285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ)) := by rw [show ((-285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ)) = -((285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((652451755824834057/6250000000000000000 : ℝ)) ≤ Real.arctan ((-285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ)) ∧ Real.arctan ((-285458170755655417856000000000000/2724535412901409471454129013822261 : ℝ)) ≤ -((652451755574834057/6250000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t22 :
    ((1508105491139106358377/1000000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 2.52 2.52 (2 * hminus) ∧ dihY (2 * hminus) 2 2 2.52 2.52 (2 * hminus) ≤ ((1508108342747988982799/1000000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2 2.52 2.52 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)) = ((-4/625 : ℝ)) * (((438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((164234716784918737688490539/24414062500000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ≤ ((4106132031300208106804559839/610351562500000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((164234716784918737688490539/24414062500000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ≤ ((4106132031300208106804559839/610351562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f8
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((164234716784918737688490539/24414062500000000000000 : ℝ)) := by norm_num
  have hs2 : ((4106132031300208106804559839/610351562500000000000000 : ℝ)) ≤ ((4101062886643655063328866436140527/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 (2 * hminus))) ≤ ((4101062886643655063328866436140527/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((62847818629/12207031250 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)) ≤ ((6435702949/1250000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) ∧ ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) := by norm_num
    have hp1 : ((62847818629/12207031250 : ℝ)) ≤ ((-4/625 : ℝ)) * (((438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ∧ ((-4/625 : ℝ)) * (((438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ≤ ((6435702949/1250000000 : ℝ)) := by
      have hf := ztgcTrioF_f28
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-6435702949/1250000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)))) ≤ ((-62847818629/12207031250 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus))))| ≤ ((6435702949/1250000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-62847818629/12207031250 : ℝ)) < ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 (2 * hminus))) ≤ -((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 (2 * hminus))) < ((-6435702949/1250000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) < ((-6435702949/1250000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-62847818629/12207031250 : ℝ)) ≤ ((-257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ)) * ((4101062886643655063328866436140527/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 (2 * hminus))) ≤ ((-257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ)) * ((4100930991710948357590082890106331/50000000000000000000000000000000 : ℝ)) ≤ ((-6435702949/1250000000 : ℝ)) := by norm_num
  have harg2 : ((-257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ))) (lo := ((62690834615790260853/1000000000000000000000 : ℝ))) (hi := ((62690834655790260853/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ)) = -Real.arctan ((257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ)) := by rw [show ((-257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ)) = -((257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((62690834655790260853/1000000000000000000000 : ℝ)) ≤ Real.arctan ((-257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ)) ∧ Real.arctan ((-257428117960000000000000000000000/4100930991710948357590082890106331 : ℝ)) ≤ -((62690834615790260853/1000000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ))) (lo := ((15671996261726909109/250000000000000000000 : ℝ))) (hi := ((15671996271726909109/250000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ)) = -Real.arctan ((257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ)) := by rw [show ((-257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ)) = -((257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((15671996271726909109/250000000000000000000 : ℝ)) ≤ Real.arctan ((-257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ)) ∧ Real.arctan ((-257424665104384000000000000000000/4101062886643655063328866436140527 : ℝ)) ≤ -((15671996261726909109/250000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t23 :
    ((87639154730486331903/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2 ∧ dihY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2 ≤ ((14022348317363934411/8000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2) = ((-4/625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((19935100950657353410477333/3051757812500000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ≤ ((6379642737829547935022927/976562500000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((19935100950657353410477333/3051757812500000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ≤ ((6379642737829547935022927/976562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f9
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((19935100950657353410477333/3051757812500000000000 : ℝ)) := by norm_num
  have hs2 : ((6379642737829547935022927/976562500000000000000 : ℝ)) ≤ ((8082545492317125053354923170442279/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2)) ≤ ((8082545492317125053354923170442279/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-145255109/9765625 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2) ≤ ((-14873729/1000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) ∧ ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) := by norm_num
    have hp1 : ((-145255109/9765625 : ℝ)) ≤ ((-4/625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ∧ ((-4/625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ≤ ((-14873729/1000000 : ℝ)) := by
      have hf := ztgcTrioF_f29
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((14873729/1000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2))) ≤ ((145255109/9765625 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2)))| ≤ ((145255109/9765625 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((145255109/9765625 : ℝ)) < ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2)) ≤ -((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2)) < ((14873729/1000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) < ((14873729/1000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((145255109/9765625 : ℝ)) := by norm_num
  have hnum : ((145255109/9765625 : ℝ)) ≤ ((1487412316160000000000000000000000/8082285493294128198245067057909789 : ℝ)) * ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2)) ≤ ((1487412316160000000000000000000000/8082285493294128198245067057909789 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((1487372900000000000000000000000000/8082545492317125053354923170442279 : ℝ)) := by norm_num
  have hnum2 : ((1487372900000000000000000000000000/8082545492317125053354923170442279 : ℝ)) * ((8082545492317125053354923170442279/100000000000000000000000000000000 : ℝ)) ≤ ((14873729/1000000 : ℝ)) := by norm_num
  have harg2 : ((1487372900000000000000000000000000/8082545492317125053354923170442279 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((1487372900000000000000000000000000/8082545492317125053354923170442279 : ℝ))) (lo := ((18198676881483001883/100000000000000000000 : ℝ))) (hi := ((18198676885483001883/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((1487412316160000000000000000000000/8082285493294128198245067057909789 : ℝ))) (lo := ((9099860591779759107/50000000000000000000 : ℝ))) (hi := ((9099860593779759107/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ ((8082545492317125053354923170442279/100000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) 8 (2 * 2) (2 * 2) := by rw [h8]
  have htlo8 : ((14873729/1000000 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) ≤ ((145255109/9765625 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2.52 (Real.sqrt 8) 2 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ -((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) < ((14873729/1000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8082285493294128198245067057909789/100000000000000000000000000000000 : ℝ)) < ((14873729/1000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t24 :
    ((14079457930791925789/10000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus) ∧ dihY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus) ≤ ((281594322133689024329/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-4/625 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((50964621070297370817944265294124377/7629394531250000000000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ≤ ((104387248352161481262939248774607/15625000000000000000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((50964621070297370817944265294124377/7629394531250000000000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ≤ ((104387248352161481262939248774607/15625000000000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f6
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((50964621070297370817944265294124377/7629394531250000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((104387248352161481262939248774607/15625000000000000000000000000 : ℝ)) ≤ ((8173606238704228414362387041466783/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus))) ≤ ((8173606238704228414362387041466783/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((1049025352562889/78125000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((1049135828668839/78125000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) ∧ ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) := by norm_num
    have hp1 : ((-15397/1953125 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) ≤ ((-4927/625000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/24414062500 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/2500000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1049025352562889/78125000000000 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ))) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ))) ≤ ((1049135828668839/78125000000000 : ℝ)) := by
      have hf := ztgcTrioF_f30
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-1049135828668839/78125000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-1049025352562889/78125000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((1049135828668839/78125000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-1049025352562889/78125000000000 : ℝ)) < ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus))) ≤ -((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus))) < ((-1049135828668839/78125000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) < ((-1049135828668839/78125000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-1049025352562889/78125000000000 : ℝ)) ≤ ((-447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ)) * ((8173606238704228414362387041466783/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus))) ≤ ((-447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-37302607241558720000000000000000/227031888717859374914446154716881 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-37302607241558720000000000000000/227031888717859374914446154716881 : ℝ)) * ((2043286998460734374230015392451929/25000000000000000000000000000000 : ℝ)) ≤ ((-1049135828668839/78125000000000 : ℝ)) := by norm_num
  have harg2 : ((-37302607241558720000000000000000/227031888717859374914446154716881 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((37302607241558720000000000000000/227031888717859374914446154716881 : ℝ))) (lo := ((16285053267570404033/100000000000000000000 : ℝ))) (hi := ((16285053271570404033/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-37302607241558720000000000000000/227031888717859374914446154716881 : ℝ)) = -Real.arctan ((37302607241558720000000000000000/227031888717859374914446154716881 : ℝ)) := by rw [show ((-37302607241558720000000000000000/227031888717859374914446154716881 : ℝ)) = -((37302607241558720000000000000000/227031888717859374914446154716881 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((16285053271570404033/100000000000000000000 : ℝ)) ≤ Real.arctan ((-37302607241558720000000000000000/227031888717859374914446154716881 : ℝ)) ∧ Real.arctan ((-37302607241558720000000000000000/227031888717859374914446154716881 : ℝ)) ≤ -((16285053267570404033/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ))) (lo := ((16282471712645149759/100000000000000000000 : ℝ))) (hi := ((16282471716645149759/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ)) = -Real.arctan ((447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ)) := by rw [show ((-447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ)) = -((447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((16282471716645149759/100000000000000000000 : ℝ)) ≤ Real.arctan ((-447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ)) ∧ Real.arctan ((-447584150426832640000000000000000/2724535412901409471454129013822261 : ℝ)) ≤ -((16282471712645149759/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t25 :
    ((194808542789480134477/125000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 (2 * hminus) 2.52 2 ∧ dihY (2 * hminus) 2 2 (2 * hminus) 2.52 2 ≤ ((389623594982798022651/250000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2 (2 * hminus) 2.52 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) = ((-12/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-3823/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) = ((-4/390625 : ℝ)) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((1568149652691977861209129937199/312500000000000000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ≤ ((149562877968631705416222121459209/29802322387695312500000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((2817331349406639/305175781250000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) ≤ ((2817470537721639/305175781250000000 : ℝ)) := by
      have hf := ztgcTrioF_f31
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((80111743822391734749231/97656250000000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) ≤ ((782390744400554849666151/953674316406250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f32
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((1568149652691977861209129937199/312500000000000000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((50/1 : ℝ)) * hminus ^ 2 + ((-113/1 : ℝ))) * (((50/1 : ℝ)) * hminus ^ 2 + ((13/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ≤ ((149562877968631705416222121459209/29802322387695312500000000000 : ℝ)) := by
      have hf := ztgcTrioF_f33
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp5.1, le_trans hp5.2 (by norm_num)⟩
  have hs1 : ((1416767996337329578420036626562539/20000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((1568149652691977861209129937199/312500000000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((149562877968631705416222121459209/29802322387695312500000000000 : ℝ)) ≤ ((7084135387274053970053872739831287/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((1416767996337329578420036626562539/20000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2.52 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2.52 2)) ≤ ((7084135387274053970053872739831287/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((136176657657417/156250000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) ≤ ((136459197619317/156250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-12/625 : ℝ)) ≤ ((-12/625 : ℝ)) ∧ ((-12/625 : ℝ)) ≤ ((-12/625 : ℝ)) := by norm_num
    have hp1 : ((-46191/1953125 : ℝ)) ≤ ((-12/625 : ℝ)) * (hminus) ∧ ((-12/625 : ℝ)) * (hminus) ≤ ((-14781/625000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-711202827/24414062500 : ℝ)) ≤ ((-12/625 : ℝ)) * (hminus) * (hminus) ∧ ((-12/625 : ℝ)) * (hminus) * (hminus) ≤ ((-72825987/2500000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((136176657657417/156250000000000 : ℝ)) ≤ ((-12/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-3823/1 : ℝ))) ∧ ((-12/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-3823/1 : ℝ))) ≤ ((136459197619317/156250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f34
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-136459197619317/156250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2))) ≤ ((-136176657657417/156250000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2)))| ≤ ((136459197619317/156250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-136176657657417/156250000000000 : ℝ)) < ((1416767996337329578420036626562539/20000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((1416767996337329578420036626562539/20000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2.52 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2.52 2)) ≤ -((1416767996337329578420036626562539/20000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2.52 2)) < ((-136459197619317/156250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((1416767996337329578420036626562539/20000000000000000000000000000000 : ℝ)) < ((-136459197619317/156250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2.52 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-1001759320698240000000000000000/81426843531885677816711180917601 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-136176657657417/156250000000000 : ℝ)) ≤ ((-1001759320698240000000000000000/81426843531885677816711180917601 : ℝ)) * ((7084135387274053970053872739831287/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2.52 2)) ≤ ((-1001759320698240000000000000000/81426843531885677816711180917601 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-1940753032808064000000000000000/157418666259703286491115180729171 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-1940753032808064000000000000000/157418666259703286491115180729171 : ℝ)) * ((1416767996337329578420036626562539/20000000000000000000000000000000 : ℝ)) ≤ ((-136459197619317/156250000000000 : ℝ)) := by norm_num
  have harg2 : ((-1940753032808064000000000000000/157418666259703286491115180729171 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) 2.52 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((1940753032808064000000000000000/157418666259703286491115180729171 : ℝ))) (lo := ((6163991719527771707/500000000000000000000 : ℝ))) (hi := ((6163991739527771707/500000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-1940753032808064000000000000000/157418666259703286491115180729171 : ℝ)) = -Real.arctan ((1940753032808064000000000000000/157418666259703286491115180729171 : ℝ)) := by rw [show ((-1940753032808064000000000000000/157418666259703286491115180729171 : ℝ)) = -((1940753032808064000000000000000/157418666259703286491115180729171 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((6163991739527771707/500000000000000000000 : ℝ)) ≤ Real.arctan ((-1940753032808064000000000000000/157418666259703286491115180729171 : ℝ)) ∧ Real.arctan ((-1940753032808064000000000000000/157418666259703286491115180729171 : ℝ)) ≤ -((6163991719527771707/500000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((1001759320698240000000000000000/81426843531885677816711180917601 : ℝ))) (lo := ((12301947863704528631/1000000000000000000000 : ℝ))) (hi := ((12301947903704528631/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-1001759320698240000000000000000/81426843531885677816711180917601 : ℝ)) = -Real.arctan ((1001759320698240000000000000000/81426843531885677816711180917601 : ℝ)) := by rw [show ((-1001759320698240000000000000000/81426843531885677816711180917601 : ℝ)) = -((1001759320698240000000000000000/81426843531885677816711180917601 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((12301947903704528631/1000000000000000000000 : ℝ)) ≤ Real.arctan ((-1001759320698240000000000000000/81426843531885677816711180917601 : ℝ)) ∧ Real.arctan ((-1001759320698240000000000000000/81426843531885677816711180917601 : ℝ)) ≤ -((12301947863704528631/1000000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t26 :
    ((401679009699154823503/250000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 2.52 2.52 2 ∧ dihY (2 * hminus) 2 2 2.52 2.52 2 ≤ ((1606726663811027490639/1000000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2 2.52 2.52 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2) = ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-3531/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2) = ((-4/390625 : ℝ)) * (((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((19120599464828988521065900151/3814697265625000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((489531102545180109506585639/97656250000000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((19120599464828988521065900151/3814697265625000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((9922500/1 : ℝ)) * hminus ^ 4 + ((-29767500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((489531102545180109506585639/97656250000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f35
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((3539897747855165844122521447987569/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((19120599464828988521065900151/3814697265625000000000000 : ℝ)) := by norm_num
  have hs2 : ((489531102545180109506585639/97656250000000000000000 : ℝ)) ≤ ((7080111927125689569819271256187687/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((3539897747855165844122521447987569/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 2)) ≤ ((7080111927125689569819271256187687/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-3883193275789381/1525878906250000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2) ≤ ((-40708003184641/16000000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) ∧ ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) := by norm_num
    have hp1 : ((-15397/1953125 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) ≤ ((-4927/625000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/24414062500 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/2500000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-3883193275789381/1525878906250000 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-3531/1 : ℝ))) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-3531/1 : ℝ))) ≤ ((-40708003184641/16000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f36
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((40708003184641/16000000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2))) ≤ ((3883193275789381/1525878906250000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2)))| ≤ ((3883193275789381/1525878906250000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((3883193275789381/1525878906250000 : ℝ)) < ((3539897747855165844122521447987569/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((3539897747855165844122521447987569/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 2)) ≤ -((3539897747855165844122521447987569/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 2)) < ((40708003184641/16000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3539897747855165844122521447987569/50000000000000000000000000000000 : ℝ)) < ((40708003184641/16000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 2)) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((3883193275789381/1525878906250000 : ℝ)) := by norm_num
  have hnum : ((3883193275789381/1525878906250000 : ℝ)) ≤ ((127244477261066436608000000000000/3539897747855165844122521447987569 : ℝ)) * ((3539897747855165844122521447987569/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 2)) ≤ ((127244477261066436608000000000000/3539897747855165844122521447987569 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((254425019904006250000000000000000/7080111927125689569819271256187687 : ℝ)) := by norm_num
  have hnum2 : ((254425019904006250000000000000000/7080111927125689569819271256187687 : ℝ)) * ((7080111927125689569819271256187687/100000000000000000000000000000000 : ℝ)) ≤ ((40708003184641/16000000000000 : ℝ)) := by norm_num
  have harg2 : ((254425019904006250000000000000000/7080111927125689569819271256187687 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2.52 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((254425019904006250000000000000000/7080111927125689569819271256187687 : ℝ))) (lo := ((17959856500861337391/500000000000000000000 : ℝ))) (hi := ((17959856520861337391/500000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((127244477261066436608000000000000/3539897747855165844122521447987569 : ℝ))) (lo := ((8982583994032717851/250000000000000000000 : ℝ))) (hi := ((8982584004032717851/250000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t27 :
    ((189496997650469481363/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2 ∧ dihY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2 ≤ ((378999948240762091857/200000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) = ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) = ((-4/390625 : ℝ)) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((13761984074582087397126541/3051757812500000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((2202163340771571009814351/488281250000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((13761984074582087397126541/3051757812500000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((2202163340771571009814351/488281250000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f37
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((13761984074582087397126541/3051757812500000000000 : ℝ)) := by norm_num
  have hs2 : ((2202163340771571009814351/488281250000000000000 : ℝ)) ≤ ((6715676080559773118660805597059619/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2)) ≤ ((6715676080559773118660805597059619/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-34435281385664381/1525878906250000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) ≤ ((-361064664931841/16000000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) ∧ ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) := by norm_num
    have hp1 : ((-15397/1953125 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) ≤ ((-4927/625000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/24414062500 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/2500000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-34435281385664381/1525878906250000 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ≤ ((-361064664931841/16000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f29
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((361064664931841/16000000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2))) ≤ ((34435281385664381/1525878906250000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2)))| ≤ ((34435281385664381/1525878906250000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((34435281385664381/1525878906250000 : ℝ)) < ((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2)) ≤ -((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2)) < ((361064664931841/16000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) < ((361064664931841/16000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((34435281385664381/1525878906250000 : ℝ)) := by norm_num
  have hnum : ((34435281385664381/1525878906250000 : ℝ)) ≤ ((1128375300445450436608000000000000/3357650570547420814394294525456091 : ℝ)) * ((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2)) ≤ ((1128375300445450436608000000000000/3357650570547420814394294525456091 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((2256654155824006250000000000000000/6715676080559773118660805597059619 : ℝ)) := by norm_num
  have hnum2 : ((2256654155824006250000000000000000/6715676080559773118660805597059619 : ℝ)) * ((6715676080559773118660805597059619/100000000000000000000000000000000 : ℝ)) ≤ ((361064664931841/16000000000000 : ℝ)) := by norm_num
  have harg2 : ((2256654155824006250000000000000000/6715676080559773118660805597059619 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((2256654155824006250000000000000000/6715676080559773118660805597059619 : ℝ))) (lo := ((405217063387247743/1250000000000000000 : ℝ))) (hi := ((405217063437247743/1250000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((1128375300445450436608000000000000/3357650570547420814394294525456091 : ℝ))) (lo := ((6484068267378276801/20000000000000000000 : ℝ))) (hi := ((6484068268178276801/20000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((12500000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ ((6715676080559773118660805597059619/100000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * 2) := by rw [h8]
  have htlo8 : ((361064664931841/16000000000000 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) ≤ ((34435281385664381/1525878906250000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2.52 2 (Real.sqrt 8) 2 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ -((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) < ((361064664931841/16000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3357650570547420814394294525456091/50000000000000000000000000000000 : ℝ)) < ((361064664931841/16000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t28 :
    ((107169943338377136969/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2.52 2 2.52 2 ∧ dihY (2 * hminus) 2 2.52 2 2.52 2 ≤ ((214344312937965285413/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2.52 2 2.52 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-8/625 : ℝ)) * (hminus) * (hminus) * (((1250/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-4/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((106472724485927370297103/19531250000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ≤ ((51990877116146117134381751/9536743164062500000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-3650129975773/11920928955078125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (hminus) ≤ ((-119604545983/390625000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((-56201051236976881/149011611938476562500 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) ≤ ((-589291598058241/1562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((106472724485927370297103/19531250000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ≤ ((51990877116146117134381751/9536743164062500000000 : ℝ)) := by
      have hf := ztgcTrioF_f38
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp5.1, le_trans hp5.2 (by norm_num)⟩
  have hs1 : ((3691681017395521244289826044418389/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((106472724485927370297103/19531250000000000000 : ℝ)) := by norm_num
  have hs2 : ((51990877116146117134381751/9536743164062500000000 : ℝ)) ≤ ((57683759719988935937597199883591/781250000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((3691681017395521244289826044418389/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 2)) ≤ ((57683759719988935937597199883591/781250000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((6288703396406639/156250000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) ≤ ((6288898949830439/156250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-8/625 : ℝ)) ≤ ((-8/625 : ℝ)) ∧ ((-8/625 : ℝ)) ≤ ((-8/625 : ℝ)) := by norm_num
    have hp1 : ((-30794/1953125 : ℝ)) ≤ ((-8/625 : ℝ)) * (hminus) ∧ ((-8/625 : ℝ)) * (hminus) ≤ ((-4927/312500 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/12207031250 : ℝ)) ≤ ((-8/625 : ℝ)) * (hminus) * (hminus) ∧ ((-8/625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((6288703396406639/156250000000000 : ℝ)) ≤ ((-8/625 : ℝ)) * (hminus) * (hminus) * (((1250/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ))) ∧ ((-8/625 : ℝ)) * (hminus) * (hminus) * (((1250/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ))) ≤ ((6288898949830439/156250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f39
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-6288898949830439/156250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2))) ≤ ((-6288703396406639/156250000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2)))| ≤ ((6288898949830439/156250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-6288703396406639/156250000000000 : ℝ)) < ((3691681017395521244289826044418389/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((3691681017395521244289826044418389/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 2)) ≤ -((3691681017395521244289826044418389/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 2)) < ((-6288898949830439/156250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3691681017395521244289826044418389/50000000000000000000000000000000 : ℝ)) < ((-6288898949830439/156250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-2418732075541015000000000000000/4437212286152995072122861529507 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-6288703396406639/156250000000000 : ℝ)) ≤ ((-2418732075541015000000000000000/4437212286152995072122861529507 : ℝ)) * ((57683759719988935937597199883591/781250000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 2)) ≤ ((-2418732075541015000000000000000/4437212286152995072122861529507 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-118379274349749440000000000000000/217157706905618896722930943789317 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-118379274349749440000000000000000/217157706905618896722930943789317 : ℝ)) * ((3691681017395521244289826044418389/50000000000000000000000000000000 : ℝ)) ≤ ((-6288898949830439/156250000000000 : ℝ)) := by norm_num
  have harg2 : ((-118379274349749440000000000000000/217157706905618896722930943789317 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 2.52 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((118379274349749440000000000000000/217157706905618896722930943789317 : ℝ))) (lo := ((24954844618556262477/50000000000000000000 : ℝ))) (hi := ((24954844620556262477/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-118379274349749440000000000000000/217157706905618896722930943789317 : ℝ)) = -Real.arctan ((118379274349749440000000000000000/217157706905618896722930943789317 : ℝ)) := by rw [show ((-118379274349749440000000000000000/217157706905618896722930943789317 : ℝ)) = -((118379274349749440000000000000000/217157706905618896722930943789317 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((24954844620556262477/50000000000000000000 : ℝ)) ≤ Real.arctan ((-118379274349749440000000000000000/217157706905618896722930943789317 : ℝ)) ∧ Real.arctan ((-118379274349749440000000000000000/217157706905618896722930943789317 : ℝ)) ≤ -((24954844618556262477/50000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((2418732075541015000000000000000/4437212286152995072122861529507 : ℝ))) (lo := ((49907476310507019217/100000000000000000000 : ℝ))) (hi := ((49907476314507019217/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-2418732075541015000000000000000/4437212286152995072122861529507 : ℝ)) = -Real.arctan ((2418732075541015000000000000000/4437212286152995072122861529507 : ℝ)) := by rw [show ((-2418732075541015000000000000000/4437212286152995072122861529507 : ℝ)) = -((2418732075541015000000000000000/4437212286152995072122861529507 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((49907476314507019217/100000000000000000000 : ℝ)) ≤ Real.arctan ((-2418732075541015000000000000000/4437212286152995072122861529507 : ℝ)) ∧ Real.arctan ((-2418732075541015000000000000000/4437212286152995072122861529507 : ℝ)) ≤ -((49907476310507019217/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t29 :
    ((5173169507298224253/5000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hplus) 2 2.52 2 ∧ dihY (2 * hminus) 2 (2 * hplus) 2 2.52 2 ≤ ((206932195976520994851/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 (2 * hplus) 2 2.52 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-83607129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((2176286965452702418358082599/390625000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ))) ≤ ((2125415989165882154692856937839/381469726562500000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((2176286965452702418358082599/390625000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2437285599990000/1 : ℝ)) * hminus ^ 2 + ((17868619582641/1 : ℝ))) ≤ ((2125415989165882154692856937839/381469726562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f40
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((186602763771715188072362282829459/2500000000000000000000000000000 : ℝ)) ^ 2 ≤ ((2176286965452702418358082599/390625000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((2125415989165882154692856937839/381469726562500000000000000 : ℝ)) ≤ ((1866087231789942602172317899239413/25000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((186602763771715188072362282829459/2500000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 2.52 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 2.52 2)) ≤ ((1866087231789942602172317899239413/25000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((27720187265637581/625000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2) ≤ ((173256319585193951/3906250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) ∧ ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/19531250000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) ≤ ((-4927/6250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/244140625000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/25000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((27720187265637581/625000000000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-83607129/1 : ℝ))) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-83607129/1 : ℝ))) ≤ ((173256319585193951/3906250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f41
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-173256319585193951/3906250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2))) ≤ ((-27720187265637581/625000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2)))| ≤ ((173256319585193951/3906250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-27720187265637581/625000000000000 : ℝ)) < ((186602763771715188072362282829459/2500000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((186602763771715188072362282829459/2500000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 2.52 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 2.52 2)) ≤ -((186602763771715188072362282829459/2500000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 2.52 2)) < ((-173256319585193951/3906250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((186602763771715188072362282829459/2500000000000000000000000000000 : ℝ)) < ((-173256319585193951/3906250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 2.52 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-27720187265637581/625000000000000 : ℝ)) ≤ ((-1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ)) * ((1866087231789942602172317899239413/25000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 2.52 2)) ≤ ((-1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-110884044534524128640000000000000/186602763771715188072362282829459 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-110884044534524128640000000000000/186602763771715188072362282829459 : ℝ)) * ((186602763771715188072362282829459/2500000000000000000000000000000 : ℝ)) ≤ ((-173256319585193951/3906250000000000 : ℝ)) := by norm_num
  have harg2 : ((-110884044534524128640000000000000/186602763771715188072362282829459 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 2.52 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((110884044534524128640000000000000/186602763771715188072362282829459 : ℝ))) (lo := ((53616242429525176863/100000000000000000000 : ℝ))) (hi := ((53616242433525176863/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-110884044534524128640000000000000/186602763771715188072362282829459 : ℝ)) = -Real.arctan ((110884044534524128640000000000000/186602763771715188072362282829459 : ℝ)) := by rw [show ((-110884044534524128640000000000000/186602763771715188072362282829459 : ℝ)) = -((110884044534524128640000000000000/186602763771715188072362282829459 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((53616242433525176863/100000000000000000000 : ℝ)) ≤ Real.arctan ((-110884044534524128640000000000000/186602763771715188072362282829459 : ℝ)) ∧ Real.arctan ((-110884044534524128640000000000000/186602763771715188072362282829459 : ℝ)) ≤ -((53616242429525176863/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ))) (lo := ((26806767395614582249/50000000000000000000 : ℝ))) (hi := ((26806767397614582249/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ)) = -Real.arctan ((1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ)) := by rw [show ((-1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ)) = -((1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((26806767397614582249/50000000000000000000 : ℝ)) ≤ Real.arctan ((-1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ)) ∧ Real.arctan ((-1108807490625503240000000000000000/1866087231789942602172317899239413 : ℝ)) ≤ -((26806767395614582249/50000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t30 :
    ((97886851619379889043/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2 ∧ dihY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2 ≤ ((195779291850156372743/200000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2) = ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((266456956881066430699597/47683715820312500000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) ≤ ((218295600444164451665831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((266456956881066430699597/47683715820312500000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) ≤ ((218295600444164451665831/39062500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f42
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((266456956881066430699597/47683715820312500000 : ℝ)) := by norm_num
  have hs2 : ((218295600444164451665831/39062500000000000000 : ℝ)) ≤ ((934442294514046100122945140367557/12500000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2)) ≤ ((934442294514046100122945140367557/12500000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((7852944908844139/156250000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2) ≤ ((7853165861056039/156250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) ∧ ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) := by norm_num
    have hp1 : ((-15397/1953125 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) ≤ ((-4927/625000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/24414062500 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/2500000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((7852944908844139/156250000000000 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ))) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-8969/1 : ℝ))) ≤ ((7853165861056039/156250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f43
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-7853165861056039/156250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2))) ≤ ((-7852944908844139/156250000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2)))| ≤ ((7853165861056039/156250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-7852944908844139/156250000000000 : ℝ)) < ((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2)) ≤ -((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2)) < ((-7853165861056039/156250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) < ((-7853165861056039/156250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-628235592707531120000000000000000/934442294514046100122945140367557 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-7852944908844139/156250000000000 : ℝ)) ≤ ((-628235592707531120000000000000000/934442294514046100122945140367557 : ℝ)) * ((934442294514046100122945140367557/12500000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2)) ≤ ((-628235592707531120000000000000000/934442294514046100122945140367557 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ)) * ((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) ≤ ((-7853165861056039/156250000000000 : ℝ)) := by norm_num
  have harg2 : ((-5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ))) (lo := ((739909761951372161/1250000000000000000 : ℝ))) (hi := ((739909762001372161/1250000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ)) = -Real.arctan ((5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ)) := by rw [show ((-5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ)) = -((5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((739909762001372161/1250000000000000000 : ℝ)) ≤ Real.arctan ((-5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ)) ∧ Real.arctan ((-5026026151075864960000000000000000/7475297586297357909724137025673373 : ℝ)) ≤ -((739909761951372161/1250000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((628235592707531120000000000000000/934442294514046100122945140367557 : ℝ))) (lo := ((1849687089200358611/3125000000000000000 : ℝ))) (hi := ((1849687089325358611/3125000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-628235592707531120000000000000000/934442294514046100122945140367557 : ℝ)) = -Real.arctan ((628235592707531120000000000000000/934442294514046100122945140367557 : ℝ)) := by rw [show ((-628235592707531120000000000000000/934442294514046100122945140367557 : ℝ)) = -((628235592707531120000000000000000/934442294514046100122945140367557 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((1849687089325358611/3125000000000000000 : ℝ)) ≤ Real.arctan ((-628235592707531120000000000000000/934442294514046100122945140367557 : ℝ)) ∧ Real.arctan ((-628235592707531120000000000000000/934442294514046100122945140367557 : ℝ)) ≤ -((1849687089200358611/3125000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-25000000/1 : ℝ)) * hminus ^ 2 + ((1062961/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ≤ ((934442294514046100122945140367557/12500000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) 8 (2 * 2) := by rw [h8]
  have htlo8 : ((-7853165861056039/156250000000000 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2)) ≤ ((-7852944908844139/156250000000000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2.52 2 (Real.sqrt 8) 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ≤ -((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) < ((-7853165861056039/156250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((7475297586297357909724137025673373/100000000000000000000000000000000 : ℝ)) < ((-7853165861056039/156250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t31 :
    ((119524682053453925961/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 2 2.52 2 ∧ dihY (2 * hminus) 2 2 2 2.52 2 ≤ ((239054588069088520241/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2 2 2.52 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((26511948066420580561189041/6103515625000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((4242228080290496567574351/976562500000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((26511948066420580561189041/6103515625000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-22422500/1 : ℝ)) * hminus ^ 2 + ((2157961/1 : ℝ))) ≤ ((4242228080290496567574351/976562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f44
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((329534428064893586955719351031177/5000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((26511948066420580561189041/6103515625000000000000 : ℝ)) := by norm_num
  have hs2 : ((4242228080290496567574351/976562500000000000000 : ℝ)) ≤ ((1647733586289352816435862893363391/25000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((329534428064893586955719351031177/5000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2.52 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2.52 2)) ≤ ((1647733586289352816435862893363391/25000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((4059924752594139/156250000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) ≤ ((4060084117056039/156250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) ∧ ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) := by norm_num
    have hp1 : ((-15397/1953125 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) ≤ ((-4927/625000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/24414062500 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/2500000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((4059924752594139/156250000000000 : ℝ)) ≤ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ))) ∧ ((-4/625 : ℝ)) * (hminus) * (hminus) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ))) ≤ ((4060084117056039/156250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f45
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-4060084117056039/156250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2))) ≤ ((-4059924752594139/156250000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2)))| ≤ ((4060084117056039/156250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-4059924752594139/156250000000000 : ℝ)) < ((329534428064893586955719351031177/5000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((329534428064893586955719351031177/5000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2.52 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2.52 2)) ≤ -((329534428064893586955719351031177/5000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2.52 2)) < ((-4060084117056039/156250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((329534428064893586955719351031177/5000000000000000000000000000000 : ℝ)) < ((-4060084117056039/156250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2.52 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-4059924752594139/156250000000000 : ℝ)) ≤ ((-649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ)) * ((1647733586289352816435862893363391/25000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2.52 2)) ≤ ((-649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-14435854638421472000000000000000/36614936451654842995079927892353 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-14435854638421472000000000000000/36614936451654842995079927892353 : ℝ)) * ((329534428064893586955719351031177/5000000000000000000000000000000 : ℝ)) ≤ ((-4060084117056039/156250000000000 : ℝ)) := by norm_num
  have harg2 : ((-14435854638421472000000000000000/36614936451654842995079927892353 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2 2.52 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((14435854638421472000000000000000/36614936451654842995079927892353 : ℝ))) (lo := ((18777475261017867981/50000000000000000000 : ℝ))) (hi := ((18777475263017867981/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-14435854638421472000000000000000/36614936451654842995079927892353 : ℝ)) = -Real.arctan ((14435854638421472000000000000000/36614936451654842995079927892353 : ℝ)) := by rw [show ((-14435854638421472000000000000000/36614936451654842995079927892353 : ℝ)) = -((14435854638421472000000000000000/36614936451654842995079927892353 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((18777475263017867981/50000000000000000000 : ℝ)) ≤ Real.arctan ((-14435854638421472000000000000000/36614936451654842995079927892353 : ℝ)) ∧ Real.arctan ((-14435854638421472000000000000000/36614936451654842995079927892353 : ℝ)) ≤ -((18777475261017867981/50000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ))) (lo := ((37552338744945401803/100000000000000000000 : ℝ))) (hi := ((37552338748945401803/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ)) = -Real.arctan ((649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ)) := by rw [show ((-649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ)) = -((649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((37552338748945401803/100000000000000000000 : ℝ)) ≤ Real.arctan ((-649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ)) ∧ Real.arctan ((-649587960415062240000000000000000/1647733586289352816435862893363391 : ℝ)) ≤ -((37552338744945401803/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t32 :
    ((71842100724228183881/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2 ∧ dihY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2 ≤ ((287378260407482166697/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-1/1562500 : ℝ)) * (((50000000/1 : ℝ)) * hminus ^ 4 + ((-75000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((53384367760921282624802224278499377/7629394531250000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((109343273396399010207884404051407/15625000000000000000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((53384367760921282624802224278499377/7629394531250000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((109343273396399010207884404051407/15625000000000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f11
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((53384367760921282624802224278499377/7629394531250000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((109343273396399010207884404051407/15625000000000000000000000000 : ℝ)) ≤ ((4182693359956499552233599564577253/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2)) ≤ ((4182693359956499552233599564577253/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((68781174820981827/6103515625000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) ≤ ((90181458300159/8000000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) ∧ ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) := by norm_num
    have hp1 : ((68781174820981827/6103515625000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (((50000000/1 : ℝ)) * hminus ^ 4 + ((-75000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ∧ ((-1/1562500 : ℝ)) * (((50000000/1 : ℝ)) * hminus ^ 4 + ((-75000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ≤ ((90181458300159/8000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f46
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-90181458300159/8000000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) ≤ ((-68781174820981827/6103515625000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2)))| ≤ ((90181458300159/8000000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-68781174820981827/6103515625000000 : ℝ)) < ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2)) ≤ -((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2)) < ((-90181458300159/8000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) < ((-90181458300159/8000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-68781174820981827/6103515625000000 : ℝ)) ≤ ((-563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ)) * ((4182693359956499552233599564577253/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2)) ≤ ((-563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-31313006354221875000000000000000/232359008278313333065472772398989 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-31313006354221875000000000000000/232359008278313333065472772398989 : ℝ)) * ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) ≤ ((-90181458300159/8000000000000 : ℝ)) := by norm_num
  have harg2 : ((-31313006354221875000000000000000/232359008278313333065472772398989 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) (2 * hminus) (2 * hminus) 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((31313006354221875000000000000000/232359008278313333065472772398989 : ℝ))) (lo := ((13395431127033294161/100000000000000000000 : ℝ))) (hi := ((13395431131033294161/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-31313006354221875000000000000000/232359008278313333065472772398989 : ℝ)) = -Real.arctan ((31313006354221875000000000000000/232359008278313333065472772398989 : ℝ)) := by rw [show ((-31313006354221875000000000000000/232359008278313333065472772398989 : ℝ)) = -((31313006354221875000000000000000/232359008278313333065472772398989 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((13395431131033294161/100000000000000000000 : ℝ)) ≤ Real.arctan ((-31313006354221875000000000000000/232359008278313333065472772398989 : ℝ)) ∧ Real.arctan ((-31313006354221875000000000000000/232359008278313333065472772398989 : ℝ)) ≤ -((13395431127033294161/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ))) (lo := ((535620103029943143/4000000000000000000 : ℝ))) (hi := ((535620103189943143/4000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ)) = -Real.arctan ((563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ)) := by rw [show ((-563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ)) = -((563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((535620103189943143/4000000000000000000 : ℝ)) ≤ Real.arctan ((-563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ)) ∧ Real.arctan ((-563455384133483126784000000000000/4182693359956499552233599564577253 : ℝ)) ≤ -((535620103029943143/4000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t33 :
    ((1477612276616231156291/1000000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2 ∧ dihY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2 ≤ ((1477616051852120319053/1000000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2) = ((-1/1562500 : ℝ)) * (((4380000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((344858720508567916296426703/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ≤ ((4311009344378920201883719391/610351562500000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((344858720508567916296426703/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3597310350000000/1 : ℝ)) * hminus ^ 2 + ((1177893369592641/1 : ℝ))) ≤ ((4311009344378920201883719391/610351562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f13
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((344858720508567916296426703/48828125000000000000000 : ℝ)) := by norm_num
  have hs2 : ((4311009344378920201883719391/610351562500000000000000 : ℝ)) ≤ ((4202129730812271138997308122291177/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2)) ≤ ((4202129730812271138997308122291177/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((191744527883/24414062500 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2) ≤ ((9817406149/1250000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) ∧ ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) := by norm_num
    have hp1 : ((191744527883/24414062500 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (((4380000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ∧ ((-1/1562500 : ℝ)) * (((4380000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ≤ ((9817406149/1250000000 : ℝ)) := by
      have hf := ztgcTrioF_f47
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-9817406149/1250000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2))) ≤ ((-191744527883/24414062500 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2)))| ≤ ((9817406149/1250000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-191744527883/24414062500 : ℝ)) < ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2)) ≤ -((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2)) < ((-9817406149/1250000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) < ((-9817406149/1250000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-20668041742336000000000000000000/221164722674330059947226743278483 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-191744527883/24414062500 : ℝ)) ≤ ((-20668041742336000000000000000000/221164722674330059947226743278483 : ℝ)) * ((4202129730812271138997308122291177/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2)) ≤ ((-20668041742336000000000000000000/221164722674330059947226743278483 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ)) * ((4201995536651404414344633485535657/50000000000000000000000000000000 : ℝ)) ≤ ((-9817406149/1250000000 : ℝ)) := by norm_num
  have harg2 : ((-392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2.52 * 2.52) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) 2.52 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ))) (lo := ((93184049138665462939/1000000000000000000000 : ℝ))) (hi := ((93184049178665462939/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ)) = -Real.arctan ((392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ)) := by rw [show ((-392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ)) = -((392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((93184049178665462939/1000000000000000000000 : ℝ)) ≤ Real.arctan ((-392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ)) ∧ Real.arctan ((-392696245960000000000000000000000/4201995536651404414344633485535657 : ℝ)) ≤ -((93184049138665462939/1000000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((20668041742336000000000000000000/221164722674330059947226743278483 : ℝ))) (lo := ((46590137971388150091/500000000000000000000 : ℝ))) (hi := ((46590137991388150091/500000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-20668041742336000000000000000000/221164722674330059947226743278483 : ℝ)) = -Real.arctan ((20668041742336000000000000000000/221164722674330059947226743278483 : ℝ)) := by rw [show ((-20668041742336000000000000000000/221164722674330059947226743278483 : ℝ)) = -((20668041742336000000000000000000/221164722674330059947226743278483 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((46590137991388150091/500000000000000000000 : ℝ)) ≤ Real.arctan ((-20668041742336000000000000000000/221164722674330059947226743278483 : ℝ)) ∧ Real.arctan ((-20668041742336000000000000000000/221164722674330059947226743278483 : ℝ)) ≤ -((46590137971388150091/500000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t34 :
    ((171546045159960499273/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2 ∧ dihY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2 ≤ ((68618783108018350749/40000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) = ((-1/1562500 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((340640702677430829037082953/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ≤ ((4258277604464001147492488927/610351562500000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((340640702677430829037082953/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) ≤ ((4258277604464001147492488927/610351562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f15
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((340640702677430829037082953/48828125000000000000000 : ℝ)) := by norm_num
  have hs2 : ((4258277604464001147492488927/610351562500000000000000 : ℝ)) ≤ ((4176350687847573168406878475314049/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2)) ≤ ((4176350687847573168406878475314049/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-475342211/39062500 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) ≤ ((-304209161/25000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) ∧ ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) := by norm_num
    have hp1 : ((-475342211/39062500 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ∧ ((-1/1562500 : ℝ)) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ≤ ((-304209161/25000000 : ℝ)) := by
      have hf := ztgcTrioF_f48
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((304209161/25000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2))) ≤ ((475342211/39062500 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2)))| ≤ ((475342211/39062500 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((475342211/39062500 : ℝ)) < ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2)) ≤ -((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2)) < ((304209161/25000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) < ((304209161/25000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((475342211/39062500 : ℝ)) := by norm_num
  have hnum : ((475342211/39062500 : ℝ)) ≤ ((1216876060160000000000000000000000/8352437722505713991522774942024841 : ℝ)) * ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2)) ≤ ((1216876060160000000000000000000000/8352437722505713991522774942024841 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((608418322000000000000000000000000/4176350687847573168406878475314049 : ℝ)) := by norm_num
  have hnum2 : ((608418322000000000000000000000000/4176350687847573168406878475314049 : ℝ)) * ((4176350687847573168406878475314049/50000000000000000000000000000000 : ℝ)) ≤ ((304209161/25000000 : ℝ)) := by norm_num
  have harg2 : ((608418322000000000000000000000000/4176350687847573168406878475314049 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((608418322000000000000000000000000/4176350687847573168406878475314049 : ℝ))) (lo := ((289328251609416747/2000000000000000000 : ℝ))) (hi := ((289328251689416747/2000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((1216876060160000000000000000000000/8352437722505713991522774942024841 : ℝ))) (lo := ((14467324986556214949/100000000000000000000 : ℝ))) (hi := ((14467324990556214949/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((982857769602641/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ ((4176350687847573168406878475314049/50000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) := by rw [h8]
  have htlo8 : ((304209161/25000000 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) ≤ ((475342211/39062500 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) (2 * hplus) (Real.sqrt 8) 2 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ -((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) < ((304209161/25000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8352437722505713991522774942024841/100000000000000000000000000000000 : ℝ)) < ((304209161/25000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t35 :
    ((27283580030678969751/20000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) ∧ dihY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((272841411735643574767/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((53384367760921282624802224278499377/7629394531250000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((109343273396399010207884404051407/15625000000000000000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((53384367760921282624802224278499377/7629394531250000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 6 + ((-1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-2668784675000000/1 : ℝ)) * hminus ^ 2 + ((1928714219602641/1 : ℝ))) ≤ ((109343273396399010207884404051407/15625000000000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f11
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((53384367760921282624802224278499377/7629394531250000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((109343273396399010207884404051407/15625000000000000000000000000 : ℝ)) ≤ ((4182693359956499552233599564577253/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus))) ≤ ((4182693359956499552233599564577253/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((10957576500514137/625000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((34245318636437463/1953125000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) ∧ ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/19531250000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) ≤ ((-4927/6250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/244140625000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/25000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((10957576500514137/625000000000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ))) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ))) ≤ ((34245318636437463/1953125000000000 : ℝ)) := by
      have hf := ztgcTrioF_f49
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-34245318636437463/1953125000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-10957576500514137/625000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((34245318636437463/1953125000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-10957576500514137/625000000000000 : ℝ)) < ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus))) ≤ -((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus))) < ((-34245318636437463/1953125000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) < ((-34245318636437463/1953125000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-10957576500514137/625000000000000 : ℝ)) ≤ ((-876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ)) * ((4182693359956499552233599564577253/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus))) ≤ ((-876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-48704453171822169600000000000000/232359008278313333065472772398989 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-48704453171822169600000000000000/232359008278313333065472772398989 : ℝ)) * ((2091231074504819997589254951590901/25000000000000000000000000000000 : ℝ)) ≤ ((-34245318636437463/1953125000000000 : ℝ)) := by norm_num
  have harg2 : ((-48704453171822169600000000000000/232359008278313333065472772398989 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((48704453171822169600000000000000/232359008278313333065472772398989 : ℝ))) (lo := ((1291358276380925823/6250000000000000000 : ℝ))) (hi := ((1291358276630925823/6250000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-48704453171822169600000000000000/232359008278313333065472772398989 : ℝ)) = -Real.arctan ((48704453171822169600000000000000/232359008278313333065472772398989 : ℝ)) := by rw [show ((-48704453171822169600000000000000/232359008278313333065472772398989 : ℝ)) = -((48704453171822169600000000000000/232359008278313333065472772398989 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((1291358276630925823/6250000000000000000 : ℝ)) ≤ Real.arctan ((-48704453171822169600000000000000/232359008278313333065472772398989 : ℝ)) ∧ Real.arctan ((-48704453171822169600000000000000/232359008278313333065472772398989 : ℝ)) ≤ -((1291358276380925823/6250000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ))) (lo := ((1032946345583393727/5000000000000000000 : ℝ))) (hi := ((1032946345783393727/5000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ)) = -Real.arctan ((876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ)) := by rw [show ((-876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ)) = -((876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((1032946345783393727/5000000000000000000 : ℝ)) ≤ Real.arctan ((-876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ)) ∧ Real.arctan ((-876606120041130960000000000000000/4182693359956499552233599564577253 : ℝ)) ≤ -((1032946345583393727/5000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t36 :
    ((60093150118513033653/40000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2 ∧ dihY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2 ≤ ((1502357249733945120841/1000000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) = ((-3/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-39639043/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((41169140225095813210501213619133/7812500000000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ≤ ((1256485128721218348774980053055247/238418579101562500000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((3065394867625389/305175781250000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) ≤ ((3065538083779239/305175781250000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f50
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((90373140765322592017581/976562500000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) ≤ ((882603235767136556475801/9536743164062500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f51
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((41169140225095813210501213619133/7812500000000000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-11627/1 : ℝ))) * (((5000/1 : ℝ)) * hminus ^ 2 + ((1627/1 : ℝ))) * (((50000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ≤ ((1256485128721218348774980053055247/238418579101562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f52
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp5.1, le_trans hp5.2 (by norm_num)⟩
  have hs1 : ((7259235461680629834345383192975733/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((41169140225095813210501213619133/7812500000000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((1256485128721218348774980053055247/238418579101562500000000000000 : ℝ)) ≤ ((7259532079504867376220795047947809/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((7259235461680629834345383192975733/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2)) ≤ ((7259532079504867376220795047947809/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((3110080310640693/625000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) ≤ ((19445325779915901/3906250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-3/1562500 : ℝ)) ≤ ((-3/1562500 : ℝ)) ∧ ((-3/1562500 : ℝ)) ≤ ((-3/1562500 : ℝ)) := by norm_num
    have hp1 : ((-46191/19531250000 : ℝ)) ≤ ((-3/1562500 : ℝ)) * (hminus) ∧ ((-3/1562500 : ℝ)) * (hminus) ≤ ((-14781/6250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-711202827/244140625000000 : ℝ)) ≤ ((-3/1562500 : ℝ)) * (hminus) * (hminus) ∧ ((-3/1562500 : ℝ)) * (hminus) * (hminus) ≤ ((-72825987/25000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((3110080310640693/625000000000000 : ℝ)) ≤ ((-3/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-39639043/1 : ℝ))) ∧ ((-3/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-39639043/1 : ℝ))) ≤ ((19445325779915901/3906250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f53
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-19445325779915901/3906250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2))) ≤ ((-3110080310640693/625000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2)))| ≤ ((19445325779915901/3906250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-3110080310640693/625000000000000 : ℝ)) < ((7259235461680629834345383192975733/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((7259235461680629834345383192975733/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2)) ≤ -((7259235461680629834345383192975733/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2)) < ((-19445325779915901/3906250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((7259235461680629834345383192975733/100000000000000000000000000000000 : ℝ)) < ((-19445325779915901/3906250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-3110080310640693/625000000000000 : ℝ)) ≤ ((-165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ)) * ((7259532079504867376220795047947809/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2)) ≤ ((-165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-55311148885094118400000000000000/806581717964514426038375910330637 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-55311148885094118400000000000000/806581717964514426038375910330637 : ℝ)) * ((7259235461680629834345383192975733/100000000000000000000000000000000 : ℝ)) ≤ ((-19445325779915901/3906250000000000 : ℝ)) := by norm_num
  have harg2 : ((-55311148885094118400000000000000/806581717964514426038375910330637 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 (2 * hminus) (2 * hplus) 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((55311148885094118400000000000000/806581717964514426038375910330637 : ℝ))) (lo := ((13693514558414155581/200000000000000000000 : ℝ))) (hi := ((13693514566414155581/200000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-55311148885094118400000000000000/806581717964514426038375910330637 : ℝ)) = -Real.arctan ((55311148885094118400000000000000/806581717964514426038375910330637 : ℝ)) := by rw [show ((-55311148885094118400000000000000/806581717964514426038375910330637 : ℝ)) = -((55311148885094118400000000000000/806581717964514426038375910330637 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((13693514566414155581/200000000000000000000 : ℝ)) ≤ Real.arctan ((-55311148885094118400000000000000/806581717964514426038375910330637 : ℝ)) ∧ Real.arctan ((-55311148885094118400000000000000/806581717964514426038375910330637 : ℝ)) ≤ -((13693514558414155581/200000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ))) (lo := ((34219539030475749197/500000000000000000000 : ℝ))) (hi := ((34219539050475749197/500000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ)) = -Real.arctan ((165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ)) := by rw [show ((-165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ)) = -((165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((34219539050475749197/500000000000000000000 : ℝ)) ≤ Real.arctan ((-165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ)) ∧ Real.arctan ((-165870949900836960000000000000000/2419844026501622458740265015982603 : ℝ)) ≤ -((34219539030475749197/500000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t37 :
    ((774674994894833503097/500000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 2 2.52 2 (2 * hplus) ∧ dihY (2 * hminus) 2 2 2.52 2 (2 * hplus) ≤ ((154935949411302198897/100000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 2 2.52 2 (2 * hplus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)) = ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-39537129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)) = ((-49/9765625000000 : ℝ)) * (((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)) = ((-49/610351562500 : ℝ)) * (hminus) * (hminus) * (((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((1291985163031743128618699500289/244140625000000000000000000 : ℝ)) ≤ ((-49/610351562500 : ℝ)) * (hminus) * (hminus) * (((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ))) ∧ ((-49/610351562500 : ℝ)) * (hminus) * (hminus) * (((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ))) ≤ ((8075613565506600841493967335519/1525878906250000000000000000 : ℝ)) := by
    have hp0 : ((-49/610351562500 : ℝ)) ≤ ((-49/610351562500 : ℝ)) ∧ ((-49/610351562500 : ℝ)) ≤ ((-49/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-754453/7629394531250000 : ℝ)) ≤ ((-49/610351562500 : ℝ)) * (hminus) ∧ ((-49/610351562500 : ℝ)) * (hminus) ≤ ((-241423/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-11616312841/95367431640625000000 : ℝ)) ≤ ((-49/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-49/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-1189491121/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((1291985163031743128618699500289/244140625000000000000000000 : ℝ)) ≤ ((-49/610351562500 : ℝ)) * (hminus) * (hminus) * (((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ))) ∧ ((-49/610351562500 : ℝ)) * (hminus) * (hminus) * (((20250000000000/1 : ℝ)) * hminus ^ 4 + ((-64173974490000/1 : ℝ)) * hminus ^ 2 + ((7303219787809/1 : ℝ))) ≤ ((8075613565506600841493967335519/1525878906250000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f54
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((1454918723197679385112768023060657/20000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((1291985163031743128618699500289/244140625000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((8075613565506600841493967335519/1525878906250000000000000000 : ℝ)) ≤ ((909363969545688820739695456797271/12500000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((1454918723197679385112768023060657/20000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2 (2 * hplus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2 (2 * hplus))) ≤ ((909363969545688820739695456797271/12500000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((974843539887581/625000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)) ≤ ((6095207127113951/3906250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) ∧ ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/19531250000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) ≤ ((-4927/6250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/244140625000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/25000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((974843539887581/625000000000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-39537129/1 : ℝ))) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-39537129/1 : ℝ))) ≤ ((6095207127113951/3906250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f55
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-6095207127113951/3906250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)))) ≤ ((-974843539887581/625000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus))))| ≤ ((6095207127113951/3906250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-974843539887581/625000000000000 : ℝ)) < ((1454918723197679385112768023060657/20000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((1454918723197679385112768023060657/20000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2 (2 * hplus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2 (2 * hplus))) ≤ -((1454918723197679385112768023060657/20000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2 (2 * hplus))) < ((-6095207127113951/3906250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((1454918723197679385112768023060657/20000000000000000000000000000000 : ℝ)) < ((-6095207127113951/3906250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2 (2 * hplus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-2785267256821660000000000000000/129909138506526974391385065256753 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-974843539887581/625000000000000 : ℝ)) ≤ ((-2785267256821660000000000000000/129909138506526974391385065256753 : ℝ)) * ((909363969545688820739695456797271/12500000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2 (2 * hplus))) ≤ ((-2785267256821660000000000000000/129909138506526974391385065256753 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-2837041862802129920000000000000/132265338472516307737524365732787 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-2837041862802129920000000000000/132265338472516307737524365732787 : ℝ)) * ((1454918723197679385112768023060657/20000000000000000000000000000000 : ℝ)) ≤ ((-6095207127113951/3906250000000000 : ℝ)) := by norm_num
  have harg2 : ((-2837041862802129920000000000000/132265338472516307737524365732787 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hplus * (2 * hplus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 2 2.52 2 (2 * hplus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((2837041862802129920000000000000/132265338472516307737524365732787 : ℝ))) (lo := ((5361583991307403259/250000000000000000000 : ℝ))) (hi := ((5361584001307403259/250000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-2837041862802129920000000000000/132265338472516307737524365732787 : ℝ)) = -Real.arctan ((2837041862802129920000000000000/132265338472516307737524365732787 : ℝ)) := by rw [show ((-2837041862802129920000000000000/132265338472516307737524365732787 : ℝ)) = -((2837041862802129920000000000000/132265338472516307737524365732787 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((5361584001307403259/250000000000000000000 : ℝ)) ≤ Real.arctan ((-2837041862802129920000000000000/132265338472516307737524365732787 : ℝ)) ∧ Real.arctan ((-2837041862802129920000000000000/132265338472516307737524365732787 : ℝ)) ≤ -((5361583991307403259/250000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((2785267256821660000000000000000/129909138506526974391385065256753 : ℝ))) (lo := ((4287366736374926053/200000000000000000000 : ℝ))) (hi := ((4287366744374926053/200000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-2785267256821660000000000000000/129909138506526974391385065256753 : ℝ)) = -Real.arctan ((2785267256821660000000000000000/129909138506526974391385065256753 : ℝ)) := by rw [show ((-2785267256821660000000000000000/129909138506526974391385065256753 : ℝ)) = -((2785267256821660000000000000000/129909138506526974391385065256753 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((4287366744374926053/200000000000000000000 : ℝ)) ≤ Real.arctan ((-2785267256821660000000000000000/129909138506526974391385065256753 : ℝ)) ∧ Real.arctan ((-2785267256821660000000000000000/129909138506526974391385065256753 : ℝ)) ≤ -((4287366736374926053/200000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t38 :
    ((36546344550887063299/20000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2 ∧ dihY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2 ≤ ((73093685520867643271/40000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) = ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((241870832660226572823470281/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ≤ ((1511852534642498725185549151/305175781250000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((241870832660226572823470281/48828125000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ≤ ((1511852534642498725185549151/305175781250000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f56
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((241870832660226572823470281/48828125000000000000000 : ℝ)) := by norm_num
  have hs2 : ((1511852534642498725185549151/305175781250000000000000 : ℝ)) ≤ ((7038493010237801538630102377311537/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2)) ≤ ((7038493010237801538630102377311537/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-112688241418543499/6103515625000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) ≤ ((-7384777468088969/400000000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) ∧ ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/19531250000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) ≤ ((-4927/6250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/244140625000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/25000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((-112688241418543499/6103515625000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-18917129/1 : ℝ))) ≤ ((-7384777468088969/400000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f48
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((7384777468088969/400000000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2))) ≤ ((112688241418543499/6103515625000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2)))| ≤ ((112688241418543499/6103515625000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((112688241418543499/6103515625000000 : ℝ)) < ((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2)) ≤ -((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2)) < ((7384777468088969/400000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) < ((7384777468088969/400000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((112688241418543499/6103515625000000 : ℝ)) := by norm_num
  have hnum : ((112688241418543499/6103515625000000 : ℝ)) ≤ ((1846284147401416687616000000000000/7038120951561816645690484381129731 : ℝ)) * ((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2)) ≤ ((1846284147401416687616000000000000/7038120951561816645690484381129731 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((1846194367022242250000000000000000/7038493010237801538630102377311537 : ℝ)) := by norm_num
  have hnum2 : ((1846194367022242250000000000000000/7038493010237801538630102377311537 : ℝ)) * ((7038493010237801538630102377311537/100000000000000000000000000000000 : ℝ)) ≤ ((7384777468088969/400000000000000 : ℝ)) := by norm_num
  have harg2 : ((1846194367022242250000000000000000/7038493010237801538630102377311537 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((1846194367022242250000000000000000/7038493010237801538630102377311537 : ℝ))) (lo := ((6413022543736413643/25000000000000000000 : ℝ))) (hi := ((6413022544736413643/25000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((1846284147401416687616000000000000/7038120951561816645690484381129731 : ℝ))) (lo := ((12827290509339723127/50000000000000000000 : ℝ))) (hi := ((12827290511339723127/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((1250000000000000/1 : ℝ)) * hminus ^ 4 + ((-3445856450000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ ((7038493010237801538630102377311537/100000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) 8 (2 * 2) (2 * 2) := by rw [h8]
  have htlo8 : ((7384777468088969/400000000000000 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2)) ≤ ((112688241418543499/6103515625000000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) (Real.sqrt 8) 2 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) ≤ -((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2))) < ((7384777468088969/400000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((7038120951561816645690484381129731/100000000000000000000000000000000 : ℝ)) < ((7384777468088969/400000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t39 :
    ((379684505358154045261/400000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2 ∧ dihY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2 ≤ ((94923906598674265287/100000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2 = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) := by unfold deltaY; rw [h8]
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) = ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((35157836475856903414617791/6103515625000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ≤ ((140640202541278166110569911/24414062500000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((35157836475856903414617791/6103515625000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) ≤ ((140640202541278166110569911/24414062500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f57
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((35157836475856903414617791/6103515625000000000000 : ℝ)) := by norm_num
  have hs2 : ((140640202541278166110569911/24414062500000000000000 : ℝ)) ≤ ((1517975322077519005453220775038257/20000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2)) ≤ ((1517975322077519005453220775038257/20000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((33977153315387581/625000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) ≤ ((212362992365833951/3906250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) ∧ ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/19531250000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) ≤ ((-4927/6250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/244140625000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/25000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((33977153315387581/625000000000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ))) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-93917129/1 : ℝ))) ≤ ((212362992365833951/3906250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f58
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-212362992365833951/3906250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2))) ≤ ((-33977153315387581/625000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2)))| ≤ ((212362992365833951/3906250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-33977153315387581/625000000000000 : ℝ)) < ((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2)) ≤ -((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2)) < ((-212362992365833951/3906250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) < ((-212362992365833951/3906250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-33977153315387581/625000000000000 : ℝ)) ≤ ((-1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) * ((1517975322077519005453220775038257/20000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2)) ≤ ((-1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) * ((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) ≤ ((-212362992365833951/3906250000000000 : ℝ)) := by norm_num
  have harg2 : ((-1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have hshlo : Real.arctan ((1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) = Real.pi / 4 + Real.arctan (((((1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ))) - 1) / ((((1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrlo : (((((1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ))) - 1) / ((((1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ))) + 1)) = ((-538286255161813437605936968303019/3256532557444488010405936968303019 : ℝ)) := by norm_num
  have htwlo := g4v_atan_pos_bounds (x := ((538286255161813437605936968303019/3256532557444488010405936968303019 : ℝ))) (lo := ((8190655049896840177/50000000000000000000 : ℝ))) (hi := ((8190655051896840177/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwlo : Real.arctan ((-538286255161813437605936968303019/3256532557444488010405936968303019 : ℝ)) = -Real.arctan ((538286255161813437605936968303019/3256532557444488010405936968303019 : ℝ)) := by rw [show ((-538286255161813437605936968303019/3256532557444488010405936968303019 : ℝ)) = -((538286255161813437605936968303019/3256532557444488010405936968303019 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnglo : Real.arctan ((-1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) = -Real.arctan ((1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) := by rw [show ((-1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) = -((1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : ((-248634024959804602431/400000000000000000000 : ℝ)) ≤ Real.arctan ((-1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) ∧ Real.arctan ((-1359123151141337286400000000000000/1897409406303150724005936968303019 : ℝ)) ≤ ((-24863402494380460243/40000000000000000000 : ℝ)) := by
    rw [hnglo, hshlo, hfrlo, hgwlo]
    constructor <;> linarith [htwlo.1, htwlo.2, hp1, hp2]
  have hshhi : Real.arctan ((1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) = Real.pi / 4 + Real.arctan (((((1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ))) - 1) / ((((1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrhi : (((((1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ))) - 1) / ((((1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ))) + 1)) = ((-430706415985116413453220775038257/2605244228169921597453220775038257 : ℝ)) := by norm_num
  have htwhi := g4v_atan_pos_bounds (x := ((430706415985116413453220775038257/2605244228169921597453220775038257 : ℝ))) (lo := ((655363606197177373/4000000000000000000 : ℝ))) (hi := ((655363606357177373/4000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwhi : Real.arctan ((-430706415985116413453220775038257/2605244228169921597453220775038257 : ℝ)) = -Real.arctan ((430706415985116413453220775038257/2605244228169921597453220775038257 : ℝ)) := by rw [show ((-430706415985116413453220775038257/2605244228169921597453220775038257 : ℝ)) = -((430706415985116413453220775038257/2605244228169921597453220775038257 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnghi : Real.arctan ((-1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) = -Real.arctan ((1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) := by rw [show ((-1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) = -((1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : ((-248622904739261586547/400000000000000000000 : ℝ)) ≤ Real.arctan ((-1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) ∧ Real.arctan ((-1087268906092402592000000000000000/1517975322077519005453220775038257 : ℝ)) ≤ ((-124311452361630793273/200000000000000000000 : ℝ)) := by
    rw [hnghi, hshhi, hfrhi, hgwhi]
    constructor <;> linarith [htwhi.1, htwhi.2, hp1, hp2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2500000000000000/1 : ℝ)) * hminus ^ 2 + ((37001319602641/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ≤ ((1517975322077519005453220775038257/20000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) 8 (2 * 2) := by rw [h8]
  have htlo8 : ((-212362992365833951/3906250000000000 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2)) ≤ ((-33977153315387581/625000000000000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hplus) 2 (Real.sqrt 8) 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) ≤ -((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hplus * (2 * hplus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2))) < ((-212362992365833951/3906250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((1897409406303150724005936968303019/25000000000000000000000000000000 : ℝ)) < ((-212362992365833951/3906250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t40 :
    ((28611950036432530491/25000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hplus) 2 2 2 2 ∧ dihY (2 * hminus) (2 * hplus) 2 2 2 2 ≤ ((228901160828958906463/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hplus) 2 2 2 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) := by rfl
  have hhpv : (2 * hplus * (2 * hplus)) = ((13254/5000) * (13254/5000)) := by
    rw [hplus]; norm_num
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) = ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ))) := by
    unfold deltaX4; rw [hhpv]; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) = ((-1/9765625000000 : ℝ)) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by
    unfold deltaX; rw [hhpv]; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) = ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((428627287690175415729025281/97656250000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ≤ ((2679122691743439736528368351/610351562500000000000000 : ℝ)) := by
    have hp0 : ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) ∧ ((-1/610351562500 : ℝ)) ≤ ((-1/610351562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/7629394531250000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) ≤ ((-4927/2441406250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/95367431640625000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((428627287690175415729025281/97656250000000000000000 : ℝ)) ≤ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ∧ ((-1/610351562500 : ℝ)) * (hminus) * (hminus) * (((625000000000000/1 : ℝ)) * hminus ^ 4 + ((-2347928225000000/1 : ℝ)) * hminus ^ 2 + ((357857769602641/1 : ℝ))) ≤ ((2679122691743439736528368351/610351562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f59
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((3312530537952559190794620474076839/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((428627287690175415729025281/97656250000000000000000 : ℝ)) := by norm_num
  have hs2 : ((2679122691743439736528368351/610351562500000000000000 : ℝ)) ≤ ((3312655512633535010655126335018841/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((3312530537952559190794620474076839/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 2)) ≤ ((3312655512633535010655126335018841/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((18805072690387581/625000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) ≤ ((117535948765833951/3906250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) ∧ ((-1/1562500 : ℝ)) ≤ ((-1/1562500 : ℝ)) := by norm_num
    have hp1 : ((-15397/19531250000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) ≤ ((-4927/6250000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/244140625000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/25000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((18805072690387581/625000000000000 : ℝ)) ≤ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ))) ∧ ((-1/1562500 : ℝ)) * (hminus) * (hminus) * (((25000000/1 : ℝ)) * hminus ^ 2 + ((-68917129/1 : ℝ))) ≤ ((117535948765833951/3906250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f60
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-117535948765833951/3906250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ≤ ((-18805072690387581/625000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)))| ≤ ((117535948765833951/3906250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-18805072690387581/625000000000000 : ℝ)) < ((3312530537952559190794620474076839/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((3312530537952559190794620474076839/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 2)) ≤ -((3312530537952559190794620474076839/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 2)) < ((-117535948765833951/3906250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3312530537952559190794620474076839/50000000000000000000000000000000 : ℝ)) < ((-117535948765833951/3906250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-18805072690387581/625000000000000 : ℝ)) ≤ ((-501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ)) * ((3312655512633535010655126335018841/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 2)) ≤ ((-501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-167162238244741619200000000000000/368058948661395465643846719341871 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-167162238244741619200000000000000/368058948661395465643846719341871 : ℝ)) * ((3312530537952559190794620474076839/50000000000000000000000000000000 : ℝ)) ≤ ((-117535948765833951/3906250000000000 : ℝ)) := by norm_num
  have harg2 : ((-167162238244741619200000000000000/368058948661395465643846719341871 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hplus * (2 * hplus)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hplus) 2 2 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((167162238244741619200000000000000/368058948661395465643846719341871 : ℝ))) (lo := ((42631832429759539959/100000000000000000000 : ℝ))) (hi := ((42631832433759539959/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-167162238244741619200000000000000/368058948661395465643846719341871 : ℝ)) = -Real.arctan ((167162238244741619200000000000000/368058948661395465643846719341871 : ℝ)) := by rw [show ((-167162238244741619200000000000000/368058948661395465643846719341871 : ℝ)) = -((167162238244741619200000000000000/368058948661395465643846719341871 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((42631832433759539959/100000000000000000000 : ℝ)) ≤ Real.arctan ((-167162238244741619200000000000000/368058948661395465643846719341871 : ℝ)) ∧ Real.arctan ((-167162238244741619200000000000000/368058948661395465643846719341871 : ℝ)) ≤ -((42631832429759539959/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ))) (lo := ((10657263091252552173/25000000000000000000 : ℝ))) (hi := ((10657263092252552173/25000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ)) = -Real.arctan ((501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ)) := by rw [show ((-501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ)) = -((501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((10657263092252552173/25000000000000000000 : ℝ)) ≤ Real.arctan ((-501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ)) ∧ Real.arctan ((-501468605077002160000000000000000/1104218504211178336885042111672947 : ℝ)) ≤ -((10657263091252552173/25000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t41 :
    ((51958550789785395683/50000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ∧ dihY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) ≤ ((207845084726220112153/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((5420357059985153/4882812500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) ≤ ((2710353909271079/2441406250000 : ℝ)) := by
      have hf := ztgcTrioF_f18
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    have hp4 : ((218306663888374772190337/78125000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) ≤ ((1066029919138303725130111/381469726562500000000 : ℝ)) := by
      have hf := ztgcTrioF_f19
      constructor <;> nlinarith [hp3.1, hp3.2, hf.1, hf.2]
    have hp5 : ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-1/1 : ℝ)) * hminus + ((-1/1 : ℝ))) * (hminus ^ 2 + ((1/1 : ℝ))) * (hminus ^ 2 + hminus + ((-1/1 : ℝ))) ≤ ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f20
      constructor <;> nlinarith [hp4.1, hp4.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp5.1, le_trans hp5.2 (by norm_num)⟩
  have hs1 : ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((6108947198480810525502250891873/1250000000000000000000000000 : ℝ)) := by norm_num
  have hs2 : ((291324772499376828078662773262099/59604644775390625000000000000 : ℝ)) ≤ ((1747787643417565377776434175478999/25000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus))) ≤ ((1747787643417565377776434175478999/25000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((328880027472641/8000000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((125467480094391899/3051757812500000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by norm_num
    have hp1 : ((328880027472641/8000000000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((2/1 : ℝ)) * hminus ^ 4 + ((-2/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((125467480094391899/3051757812500000 : ℝ)) := by
      have hf := ztgcTrioF_f61
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-125467480094391899/3051757812500000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-328880027472641/8000000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((125467480094391899/3051757812500000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-328880027472641/8000000000000 : ℝ)) < ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus))) ≤ -((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus))) < ((-125467480094391899/3051757812500000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) < ((-125467480094391899/3051757812500000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-328880027472641/8000000000000 : ℝ)) ≤ ((-1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ)) * ((1747787643417565377776434175478999/25000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus))) ≤ ((-1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ)) * ((6990820952352127489890476478026019/100000000000000000000000000000000 : ℝ)) ≤ ((-125467480094391899/3051757812500000 : ℝ)) := by norm_num
  have harg2 : ((-4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (2 * hminus) 2 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ))) (lo := ((53162530995918870557/100000000000000000000 : ℝ))) (hi := ((53162530999918870557/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ)) = -Real.arctan ((4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ)) := by rw [show ((-4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ)) = -((4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((53162530999918870557/100000000000000000000 : ℝ)) ≤ Real.arctan ((-4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ)) ∧ Real.arctan ((-4111318387733033746432000000000000/6990820952352127489890476478026019 : ℝ)) ≤ -((53162530995918870557/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ))) (lo := ((53157090416379605847/100000000000000000000 : ℝ))) (hi := ((53157090420379605847/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ)) = -Real.arctan ((1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ)) := by rw [show ((-1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ)) = -((1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((53157090420379605847/100000000000000000000 : ℝ)) ≤ Real.arctan ((-1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ)) ∧ Real.arctan ((-1027750085852003125000000000000000/1747787643417565377776434175478999 : ℝ)) ≤ -((53157090416379605847/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t42 :
    ((101438567402920726463/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (2 * hminus) 2 2 2.52 2 ∧ dihY (2 * hminus) (2 * hminus) 2 2 2.52 2 ≤ ((202882199970615821293/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY (2 * hminus) (2 * hminus) 2 2 2.52 2 = deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) := by rfl
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) = ((4/625 : ℝ)) * (((5438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) = ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((118892084664640922922865539/24414062500000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ≤ ((2972520368903210204693839839/610351562500000000000000 : ℝ)) := by
    have hp0 : ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) ∧ ((-64/390625 : ℝ)) ≤ ((-64/390625 : ℝ)) := by norm_num
    have hp1 : ((-246352/1220703125 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) ≤ ((-9854/48828125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-948270436/3814697265625 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/97656250000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((118892084664640922922865539/24414062500000000000000 : ℝ)) ≤ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ∧ ((-64/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ≤ ((2972520368903210204693839839/610351562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f22
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((118892084664640922922865539/24414062500000000000000 : ℝ)) := by norm_num
  have hs2 : ((2972520368903210204693839839/610351562500000000000000 : ℝ)) ≤ ((872333201499998526632014999898033/12500000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2.52 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2.52 2)) ≤ ((872333201499998526632014999898033/12500000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((54252619551/1250000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2) ≤ ((529821203871/12207031250 : ℝ)) := by
    rw [hE4]
    have hp0 : ((4/625 : ℝ)) ≤ ((4/625 : ℝ)) ∧ ((4/625 : ℝ)) ≤ ((4/625 : ℝ)) := by norm_num
    have hp1 : ((54252619551/1250000000 : ℝ)) ≤ ((4/625 : ℝ)) * (((5438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ∧ ((4/625 : ℝ)) * (((5438/1 : ℝ)) * hminus ^ 2 + ((-1469/1 : ℝ))) ≤ ((529821203871/12207031250 : ℝ)) := by
      have hf := ztgcTrioF_f62
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-529821203871/12207031250 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2))) ≤ ((-54252619551/1250000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2)))| ≤ ((529821203871/12207031250 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-54252619551/1250000000 : ℝ)) < ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2.52 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2.52 2)) ≤ -((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2.52 2)) < ((-529821203871/12207031250 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) < ((-529821203871/12207031250 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2.52 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-542526195510000000000000000000000/872333201499998526632014999898033 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-54252619551/1250000000 : ℝ)) ≤ ((-542526195510000000000000000000000/872333201499998526632014999898033 : ℝ)) * ((872333201499998526632014999898033/12500000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2.52 2)) ≤ ((-542526195510000000000000000000000/872333201499998526632014999898033 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ)) * ((6978409408929512503605910704177123/100000000000000000000000000000000 : ℝ)) ≤ ((-529821203871/12207031250 : ℝ)) := by norm_num
  have harg2 : ((-1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) (2.52 * 2.52) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (2 * hminus) 2 2 2.52 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ))) (lo := ((2782053258628446773/5000000000000000000 : ℝ))) (hi := ((2782053258828446773/5000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ)) = -Real.arctan ((1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ)) := by rw [show ((-1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ)) = -((1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((2782053258828446773/5000000000000000000 : ℝ)) ≤ Real.arctan ((-1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ)) ∧ Real.arctan ((-1446765100703744000000000000000000/2326136469643170834535303568059041 : ℝ)) ≤ -((2782053258628446773/5000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((542526195510000000000000000000000/872333201499998526632014999898033 : ℝ))) (lo := ((55638532794181751277/100000000000000000000 : ℝ))) (hi := ((55638532798181751277/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-542526195510000000000000000000000/872333201499998526632014999898033 : ℝ)) = -Real.arctan ((542526195510000000000000000000000/872333201499998526632014999898033 : ℝ)) := by rw [show ((-542526195510000000000000000000000/872333201499998526632014999898033 : ℝ)) = -((542526195510000000000000000000000/872333201499998526632014999898033 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((55638532798181751277/100000000000000000000 : ℝ)) ≤ Real.arctan ((-542526195510000000000000000000000/872333201499998526632014999898033 : ℝ)) ∧ Real.arctan ((-542526195510000000000000000000000/872333201499998526632014999898033 : ℝ)) ≤ -((55638532794181751277/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t43 :
    ((1713321043047674165203/2000000000000000000000 : ℝ)) ≤ dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ∧ dihY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) ≤ ((856690339255206968971/1000000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus) = deltaX (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ)) := by norm_num
  have hs2 : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus))) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((56825987/1000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((554952827/9765625 : ℝ)) := by
    rw [hE4]
    have hp0 : ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) ∧ ((16/1 : ℝ)) ≤ ((16/1 : ℝ)) := by norm_num
    have hp1 : ((56825987/1000000 : ℝ)) ≤ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ∧ ((16/1 : ℝ)) * (((3/1 : ℝ)) * hminus ^ 2 + ((-1/1 : ℝ))) ≤ ((554952827/9765625 : ℝ)) := by
      have hf := ztgcTrioF_f63
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-554952827/9765625 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-56825987/1000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((554952827/9765625 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-56825987/1000000 : ℝ)) < ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus))) ≤ -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus))) < ((-554952827/9765625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) < ((-554952827/9765625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-56825987/1000000 : ℝ)) ≤ ((-5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) * ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus))) ≤ ((-5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) * ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ ((-554952827/9765625 : ℝ)) := by norm_num
  have harg2 : ((-39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have hshlo : Real.arctan ((39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) = Real.pi / 4 + Real.arctan (((((39739279360000000000000000000000/45848835979366290048003842696151 : ℝ))) - 1) / ((((39739279360000000000000000000000/45848835979366290048003842696151 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrlo : (((((39739279360000000000000000000000/45848835979366290048003842696151 : ℝ))) - 1) / ((((39739279360000000000000000000000/45848835979366290048003842696151 : ℝ))) + 1)) = ((-6109556619366290048003842696151/85588115339366290048003842696151 : ℝ)) := by norm_num
  have htwlo := g4v_atan_pos_bounds (x := ((6109556619366290048003842696151/85588115339366290048003842696151 : ℝ))) (lo := ((71262359126388772989/1000000000000000000000 : ℝ))) (hi := ((71262359166388772989/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwlo : Real.arctan ((-6109556619366290048003842696151/85588115339366290048003842696151 : ℝ)) = -Real.arctan ((6109556619366290048003842696151/85588115339366290048003842696151 : ℝ)) := by rw [show ((-6109556619366290048003842696151/85588115339366290048003842696151 : ℝ)) = -((6109556619366290048003842696151/85588115339366290048003842696151 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnglo : Real.arctan ((-39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) = -Real.arctan ((39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) := by rw [show ((-39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) = -((39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : ((-1428271608542119073257/2000000000000000000000 : ℝ)) ≤ Real.arctan ((-39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) ∧ Real.arctan ((-39739279360000000000000000000000/45848835979366290048003842696151 : ℝ)) ≤ ((-357067902115529768313/500000000000000000000 : ℝ)) := by
    rw [hnglo, hshlo, hfrlo, hgwlo]
    constructor <;> linarith [htwlo.1, htwlo.2, hp1, hp2]
  have hshhi : Real.arctan ((5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) = Real.pi / 4 + Real.arctan (((((5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ))) - 1) / ((((5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrhi : (((((5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ))) - 1) / ((((5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ))) + 1)) = ((-874043393309874663320933098090969/12239240793309874663320933098090969 : ℝ)) := by norm_num
  have htwhi := g4v_atan_pos_bounds (x := ((874043393309874663320933098090969/12239240793309874663320933098090969 : ℝ))) (lo := ((71292174817758659351/1000000000000000000000 : ℝ))) (hi := ((71292174857758659351/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwhi : Real.arctan ((-874043393309874663320933098090969/12239240793309874663320933098090969 : ℝ)) = -Real.arctan ((874043393309874663320933098090969/12239240793309874663320933098090969 : ℝ)) := by rw [show ((-874043393309874663320933098090969/12239240793309874663320933098090969 : ℝ)) = -((874043393309874663320933098090969/12239240793309874663320933098090969 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnghi : Real.arctan ((-5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) = -Real.arctan ((5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) := by rw [show ((-5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) = -((5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : ((-1428211977159379300533/2000000000000000000000 : ℝ)) ≤ Real.arctan ((-5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) ∧ Real.arctan ((-5682598700000000000000000000000000/6556642093309874663320933098090969 : ℝ)) ≤ ((-89263248567461206283/125000000000000000000 : ℝ)) := by
    rw [hnghi, hshhi, hfrhi, hgwhi]
    constructor <;> linarith [htwhi.1, htwhi.2, hp1, hp2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) = deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) 8 (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) := by rw [h8]
  have htlo8 : ((-554952827/9765625 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus))) ≤ ((-56825987/1000000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) 2 (Real.sqrt 8) 2 2 (2 * hminus))) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)))) < ((-554952827/9765625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) < ((-554952827/9765625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t44 :
    ((106870594681673489937/100000000000000000000 : ℝ)) ≤ dihY (2 * hminus) (Real.sqrt 8) 2 2 2 2 ∧ dihY (2 * hminus) (Real.sqrt 8) 2 2 2 2 ≤ ((213747288495744806849/200000000000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2 = deltaX (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2 = deltaX (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2) = ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2) = ((-64/1 : ℝ)) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
    have hp0 : ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) ∧ ((-1024/1 : ℝ)) ≤ ((-1024/1 : ℝ)) := by norm_num
    have hp1 : ((-3941632/3125 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) ≤ ((-157664/125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-15172326976/9765625 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/15625 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((204974008511520043980847/47683715820312500000 : ℝ)) ≤ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ∧ ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) ≤ ((167927951327195450705831/39062500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f1
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((204974008511520043980847/47683715820312500000 : ℝ)) := by norm_num
  have hs2 : ((167927951327195450705831/39062500000000000000 : ℝ)) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2)) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2)) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((5624166265031639/156250000000000 : ℝ)) ≤ deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ∧ deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2) ≤ ((5624351028281639/156250000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) ∧ ((-16/1 : ℝ)) ≤ ((-16/1 : ℝ)) := by norm_num
    have hp1 : ((-61588/3125 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) ≤ ((-4927/250 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-237067609/9765625 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) ≤ ((-24275329/1000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((5624166265031639/156250000000000 : ℝ)) ≤ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ∧ ((-16/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 2 + ((-3/1 : ℝ))) ≤ ((5624351028281639/156250000000000 : ℝ)) := by
      have hf := ztgcTrioF_f23
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have htlo : ((-5624351028281639/156250000000000 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ≤ ((-5624166265031639/156250000000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2)))| ≤ ((5624351028281639/156250000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-5624166265031639/156250000000000 : ℝ)) < ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2)) ≤ -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2)) < ((-5624351028281639/156250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) < ((-5624351028281639/156250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-5624166265031639/156250000000000 : ℝ)) ≤ ((-3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ)) * ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2)) ≤ ((-3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ)) * ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ ((-5624351028281639/156250000000000 : ℝ)) := by norm_num
  have harg2 : ((-3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ)) ≤ (-(deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ))) (lo := ((25104518946908085993/50000000000000000000 : ℝ))) (hi := ((25104518948908085993/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ)) = -Real.arctan ((3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ)) := by rw [show ((-3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ)) = -((3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((25104518948908085993/50000000000000000000 : ℝ)) ≤ Real.arctan ((-3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ)) ∧ Real.arctan ((-3599584658100248960000000000000000/6556383545049379476864549505549593 : ℝ)) ≤ -((25104518946908085993/50000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ))) (lo := ((50205988531617258499/100000000000000000000 : ℝ))) (hi := ((50205988535617258499/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ)) = -Real.arctan ((3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ)) := by rw [show ((-3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ)) = -((3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((50205988535617258499/100000000000000000000 : ℝ)) ≤ Real.arctan ((-3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ)) ∧ Real.arctan ((-3599466409620248960000000000000000/6556642093309874663320933098090969 : ℝ)) ≤ -((50205988531617258499/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) = ((-1024/1 : ℝ)) * (hminus) * (hminus) * (hminus ^ 4 + ((-4/1 : ℝ)) * hminus ^ 2 + ((1/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ∧ (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ≤ ((6556642093309874663320933098090969/100000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2) = deltaX4 (2 * hminus * (2 * hminus)) 8 (2 * 2) (2 * 2) (2 * 2) (2 * 2) := by rw [h8]
  have htlo8 : ((-5624351028281639/156250000000000 : ℝ)) ≤ -(deltaX4 (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2)) ≤ ((-5624166265031639/156250000000000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))| < (Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaY (2 * hminus) (Real.sqrt 8) 2 2 2 2)) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) ≤ -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2 * hminus * (2 * hminus)) * deltaX (2 * hminus * (2 * hminus)) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * 2) (2 * 2) (2 * 2))) < ((-5624351028281639/156250000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((6556383545049379476864549505549593/100000000000000000000000000000000 : ℝ)) < ((-5624351028281639/156250000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t45 :
    ((20655510982699535937/20000000000000000000 : ℝ)) ≤ dihY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ∧ dihY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 ≤ ((41312528297451453183/40000000000000000000 : ℝ)) := by
  have hEbrid : deltaY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2 = deltaX (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) := by rfl
  have hE4 : deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((3969/390625 : ℝ)) * (((7500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((8332681341950515470930210212697/1192092895507812500000000000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ≤ ((1747657516171806158185894887/250000000000000000000000 : ℝ)) := by
    have hp0 : ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) ∧ ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) := by norm_num
    have hp1 : ((8332681341950515470930210212697/1192092895507812500000000000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 6 + ((-12500000/1 : ℝ)) * hminus ^ 4 + ((-23517500/1 : ℝ)) * hminus ^ 2 + ((15752961/1 : ℝ))) ≤ ((1747657516171806158185894887/250000000000000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f6
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hs1 : ((2090149476809843971205231901351273/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((8332681341950515470930210212697/1192092895507812500000000000 : ℝ)) := by norm_num
  have hs2 : ((1747657516171806158185894887/250000000000000000000000 : ℝ)) ≤ ((8360998782853256967287828531733573/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((2090149476809843971205231901351273/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2)) ∧ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2)) ≤ ((8360998782853256967287828531733573/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((124723392003/2500000000 : ℝ)) ≤ deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((1218047707863/24414062500 : ℝ)) := by
    rw [hE4]
    have hp0 : ((3969/390625 : ℝ)) ≤ ((3969/390625 : ℝ)) ∧ ((3969/390625 : ℝ)) ≤ ((3969/390625 : ℝ)) := by norm_num
    have hp1 : ((124723392003/2500000000 : ℝ)) ≤ ((3969/390625 : ℝ)) * (((7500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ))) ∧ ((3969/390625 : ℝ)) * (((7500/1 : ℝ)) * hminus ^ 2 + ((-6469/1 : ℝ))) ≤ ((1218047707863/24414062500 : ℝ)) := by
      have hf := ztgcTrioF_f64
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-1218047707863/24414062500 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) ≤ ((-124723392003/2500000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)))| ≤ ((1218047707863/24414062500 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-124723392003/2500000000 : ℝ)) < ((2090149476809843971205231901351273/25000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((2090149476809843971205231901351273/25000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)))| < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2)) ≤ -((2090149476809843971205231901351273/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2)) < ((-1218047707863/24414062500 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((2090149476809843971205231901351273/25000000000000000000000000000000 : ℝ)) < ((-1218047707863/24414062500 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-124723392003/2500000000 : ℝ)) ≤ ((-1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ)) * ((8360998782853256967287828531733573/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2)) ≤ ((-1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-138586761427968000000000000000000/232238830756649330133914655705697 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-138586761427968000000000000000000/232238830756649330133914655705697 : ℝ)) * ((2090149476809843971205231901351273/25000000000000000000000000000000 : ℝ)) ≤ ((-1218047707863/24414062500 : ℝ)) := by norm_num
  have harg2 : ((-138586761427968000000000000000000/232238830756649330133914655705697 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) (2 * hminus) 2 (2 * hminus) 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((138586761427968000000000000000000/232238830756649330133914655705697 : ℝ))) (lo := ((26901038830995991119/50000000000000000000 : ℝ))) (hi := ((26901038832995991119/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-138586761427968000000000000000000/232238830756649330133914655705697 : ℝ)) = -Real.arctan ((138586761427968000000000000000000/232238830756649330133914655705697 : ℝ)) := by rw [show ((-138586761427968000000000000000000/232238830756649330133914655705697 : ℝ)) = -((138586761427968000000000000000000/232238830756649330133914655705697 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((26901038832995991119/50000000000000000000 : ℝ)) ≤ Real.arctan ((-138586761427968000000000000000000/232238830756649330133914655705697 : ℝ)) ∧ Real.arctan ((-138586761427968000000000000000000/232238830756649330133914655705697 : ℝ)) ≤ -((26901038830995991119/50000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ))) (lo := ((26899156017930514483/50000000000000000000 : ℝ))) (hi := ((26899156019930514483/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ)) = -Real.arctan ((1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ)) := by rw [show ((-1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ)) = -((1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((26899156019930514483/50000000000000000000 : ℝ)) ≤ Real.arctan ((-1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ)) ∧ Real.arctan ((-1662978560040000000000000000000000/2786999594284418989095942843911191 : ℝ)) ≤ -((26899156017930514483/50000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t46 :
    ((2027398434405461557/2000000000000000000 : ℝ)) ≤ dihY 2.52 2.52 2 2 (2 * hminus) (2 * hminus) ∧ dihY 2.52 2.52 2 2 (2 * hminus) (2 * hminus) ≤ ((202747957067890057373/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY 2.52 2.52 2 2 (2 * hminus) (2 * hminus) = deltaX (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-4/625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-14407/1 : ℝ)) * hminus ^ 2 + ((7938/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((26852265974205435892779/3814697265625000000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ≤ ((68745106516135344225399/9765625000000000000 : ℝ)) := by
    have hp0 : ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) ∧ ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) := by norm_num
    have hp1 : ((26852265974205435892779/3814697265625000000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-33859539/1 : ℝ)) * hminus ^ 2 + ((9922500/1 : ℝ))) ≤ ((68745106516135344225399/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f8
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hs1 : ((2097492611956888544973880430904801/25000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((26852265974205435892779/3814697265625000000 : ℝ)) := by norm_num
  have hs2 : ((68745106516135344225399/9765625000000000000 : ℝ)) ≤ ((8390172171804581054421718044971527/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((2097492611956888544973880430904801/25000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2.52 2 2 (2 * hminus) (2 * hminus))) ∧ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2.52 2 2 (2 * hminus) (2 * hminus))) ≤ ((8390172171804581054421718044971527/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((1275848267151729279/24414062500000000 : ℝ)) ≤ deltaX4 (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((20904885022811367/400000000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) ∧ ((-4/625 : ℝ)) ≤ ((-4/625 : ℝ)) := by norm_num
    have hp1 : ((1275848267151729279/24414062500000000 : ℝ)) ≤ ((-4/625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-14407/1 : ℝ)) * hminus ^ 2 + ((7938/1 : ℝ))) ∧ ((-4/625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-14407/1 : ℝ)) * hminus ^ 2 + ((7938/1 : ℝ))) ≤ ((20904885022811367/400000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f65
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-20904885022811367/400000000000000 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ≤ ((-1275848267151729279/24414062500000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| ≤ ((20904885022811367/400000000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-1275848267151729279/24414062500000000 : ℝ)) < ((2097492611956888544973880430904801/25000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((2097492611956888544973880430904801/25000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2.52 2 2 (2 * hminus) (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2.52 2 2 (2 * hminus) (2 * hminus))) ≤ -((2097492611956888544973880430904801/25000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2.52 2 2 (2 * hminus) (2 * hminus))) < ((-20904885022811367/400000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((2097492611956888544973880430904801/25000000000000000000000000000000 : ℝ)) < ((-20904885022811367/400000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2.52 2 2 (2 * hminus) (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-180202569043223556096000000000000/289316281786364863945576484309363 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-1275848267151729279/24414062500000000 : ℝ)) ≤ ((-180202569043223556096000000000000/289316281786364863945576484309363 : ℝ)) * ((8390172171804581054421718044971527/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2.52 2 2 (2 * hminus) (2 * hminus))) ≤ ((-180202569043223556096000000000000/289316281786364863945576484309363 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-435518437975236812500000000000000/699164203985629514991293476968267 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-435518437975236812500000000000000/699164203985629514991293476968267 : ℝ)) * ((2097492611956888544973880430904801/25000000000000000000000000000000 : ℝ)) ≤ ((-20904885022811367/400000000000000 : ℝ)) := by norm_num
  have harg2 : ((-435518437975236812500000000000000/699164203985629514991293476968267 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2.52 * 2.52) (2 * 2) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2.52 2 2 (2 * hminus) (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((435518437975236812500000000000000/699164203985629514991293476968267 : ℝ))) (lo := ((55709710855216584073/100000000000000000000 : ℝ))) (hi := ((55709710859216584073/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-435518437975236812500000000000000/699164203985629514991293476968267 : ℝ)) = -Real.arctan ((435518437975236812500000000000000/699164203985629514991293476968267 : ℝ)) := by rw [show ((-435518437975236812500000000000000/699164203985629514991293476968267 : ℝ)) = -((435518437975236812500000000000000/699164203985629514991293476968267 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((55709710859216584073/100000000000000000000 : ℝ)) ≤ Real.arctan ((-435518437975236812500000000000000/699164203985629514991293476968267 : ℝ)) ∧ Real.arctan ((-435518437975236812500000000000000/699164203985629514991293476968267 : ℝ)) ≤ -((55709710855216584073/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((180202569043223556096000000000000/289316281786364863945576484309363 : ℝ))) (lo := ((55705654245544633237/100000000000000000000 : ℝ))) (hi := ((55705654249544633237/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-180202569043223556096000000000000/289316281786364863945576484309363 : ℝ)) = -Real.arctan ((180202569043223556096000000000000/289316281786364863945576484309363 : ℝ)) := by rw [show ((-180202569043223556096000000000000/289316281786364863945576484309363 : ℝ)) = -((180202569043223556096000000000000/289316281786364863945576484309363 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((55705654249544633237/100000000000000000000 : ℝ)) ≤ Real.arctan ((-180202569043223556096000000000000/289316281786364863945576484309363 : ℝ)) ∧ Real.arctan ((-180202569043223556096000000000000/289316281786364863945576484309363 : ℝ)) ≤ -((55705654245544633237/100000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t47 :
    ((358394044511127596341/400000000000000000000 : ℝ)) ≤ dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ∧ dihY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) ≤ ((5600147596286243/6250000000000000 : ℝ)) := by
  have h8 : (Real.sqrt 8 * (Real.sqrt 8)) = 8 := Real.mul_self_sqrt (by norm_num)
  have hEbrid : deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) = deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) := by unfold deltaY; rw [h8]
  have hEbrid8 : deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus) = deltaX (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) := by unfold deltaY; rw [h8]
  have hE4 : deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-1/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-38595000/1 : ℝ)) * hminus ^ 2 + ((18330461/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((3259375626717933902613/476837158203125000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ≤ ((106808357891041436007/15625000000000000 : ℝ)) := by
    have hp0 : ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) ∧ ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) := by norm_num
    have hp1 : ((3259375626717933902613/476837158203125000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) ≤ ((106808357891041436007/15625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f9
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hs1 : ((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((3259375626717933902613/476837158203125000 : ℝ)) := by norm_num
  have hs2 : ((106808357891041436007/15625000000000000 : ℝ)) ≤ ((2066962582061354802725820613341331/25000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus))) ∧ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus))) ≤ ((2066962582061354802725820613341331/25000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((807459845485044327/12207031250000000 : ℝ)) ≤ deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) ≤ ((26460296251548903/400000000000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-1/390625 : ℝ)) ≤ ((-1/390625 : ℝ)) ∧ ((-1/390625 : ℝ)) ≤ ((-1/390625 : ℝ)) := by norm_num
    have hp1 : ((807459845485044327/12207031250000000 : ℝ)) ≤ ((-1/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-38595000/1 : ℝ)) * hminus ^ 2 + ((18330461/1 : ℝ))) ∧ ((-1/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-38595000/1 : ℝ)) * hminus ^ 2 + ((18330461/1 : ℝ))) ≤ ((26460296251548903/400000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f66
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-26460296251548903/400000000000000 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ≤ ((-807459845485044327/12207031250000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| ≤ ((26460296251548903/400000000000000 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-807459845485044327/12207031250000000 : ℝ)) < ((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus))) ≤ -((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus))) < ((-26460296251548903/400000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) < ((-26460296251548903/400000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-807459845485044327/12207031250000000 : ℝ)) ≤ ((-1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) * ((2066962582061354802725820613341331/25000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus))) ≤ ((-1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) * ((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) ≤ ((-26460296251548903/400000000000000 : ℝ)) := by norm_num
  have harg2 : ((-367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have hshlo : Real.arctan ((367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) = Real.pi / 4 + Real.arctan (((((367504114604845875000000000000000/459313971609976840982506122407881 : ℝ))) - 1) / ((((367504114604845875000000000000000/459313971609976840982506122407881 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrlo : (((((367504114604845875000000000000000/459313971609976840982506122407881 : ℝ))) - 1) / ((((367504114604845875000000000000000/459313971609976840982506122407881 : ℝ))) + 1)) = ((-91809857005130965982506122407881/826818086214822715982506122407881 : ℝ)) := by norm_num
  have htwlo := g4v_atan_pos_bounds (x := ((91809857005130965982506122407881/826818086214822715982506122407881 : ℝ))) (lo := ((2764673722009267031/25000000000000000000 : ℝ))) (hi := ((2764673723009267031/25000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwlo : Real.arctan ((-91809857005130965982506122407881/826818086214822715982506122407881 : ℝ)) = -Real.arctan ((91809857005130965982506122407881/826818086214822715982506122407881 : ℝ)) := by rw [show ((-91809857005130965982506122407881/826818086214822715982506122407881 : ℝ)) = -((91809857005130965982506122407881/826818086214822715982506122407881 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnglo : Real.arctan ((-367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) = -Real.arctan ((367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) := by rw [show ((-367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) = -((367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : ((-269924485806831051351/400000000000000000000 : ℝ)) ≤ Real.arctan ((-367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) ∧ Real.arctan ((-367504114604845875000000000000000/459313971609976840982506122407881 : ℝ)) ≤ ((-5398489715816621027/8000000000000000000 : ℝ)) := by
    rw [hnglo, hshlo, hfrlo, hgwlo]
    constructor <;> linarith [htwlo.1, htwlo.2, hp1, hp2]
  have hshhi : Real.arctan ((1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) = Real.pi / 4 + Real.arctan (((((1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ))) - 1) / ((((1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ))) + 1)) := ztg_atan_shift_add (by norm_num)
  have hfrhi : (((((1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ))) - 1) / ((((1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ))) + 1)) = ((-413284818507984021029820613341331/3720640345614725584421820613341331 : ℝ)) := by norm_num
  have htwhi := g4v_atan_pos_bounds (x := ((413284818507984021029820613341331/3720640345614725584421820613341331 : ℝ))) (lo := ((5531272548417528519/50000000000000000000 : ℝ))) (hi := ((5531272550417528519/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hgwhi : Real.arctan ((-413284818507984021029820613341331/3720640345614725584421820613341331 : ℝ)) = -Real.arctan ((413284818507984021029820613341331/3720640345614725584421820613341331 : ℝ)) := by rw [show ((-413284818507984021029820613341331/3720640345614725584421820613341331 : ℝ)) = -((413284818507984021029820613341331/3720640345614725584421820613341331 : ℝ)) from by norm_num, Real.arctan_neg]
  have hnghi : Real.arctan ((-1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) = -Real.arctan ((1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) := by rw [show ((-1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) = -((1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : ((-53981816994327819139/80000000000000000000 : ℝ)) ≤ Real.arctan ((-1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) ∧ Real.arctan ((-1653677763553370781696000000000000/2066962582061354802725820613341331 : ℝ)) ≤ ((-134954542477819547847/200000000000000000000 : ℝ)) := by
    rw [hnghi, hshhi, hfrhi, hgwhi]
    constructor <;> linarith [htwhi.1, htwhi.2, hp1, hp2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  have hEA8 : 4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-32345000/1 : ℝ)) * hminus ^ 2 + ((8407961/1 : ℝ))) := by rw [h8]; exact hEA
  have hsqX : ((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ∧ (Real.sqrt (4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ≤ ((2066962582061354802725820613341331/25000000000000000000000000000000 : ℝ)) := by
    rw [hEA8]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h48 : deltaX4 (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) = deltaX4 (2.52 * 2.52) (2 * 2) 8 (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) := by rw [h8]
  have htlo8 : ((-26460296251548903/400000000000000 : ℝ)) ≤ -(deltaX4 (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) := by rw [h48]; exact htlo
  have hthi8 : -(deltaX4 (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus))) ≤ ((-807459845485044327/12207031250000000 : ℝ)) := by rw [h48]; exact hthi
  have hbrX : |-(deltaX4 (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))| < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (Real.sqrt 8) 2 (2 * hminus) (2 * hminus))) := by
    rw [abs_lt, hEbrid8]
    have hn : -(Real.sqrt (4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) ≤ -((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsqX.1
    have h1 : -(Real.sqrt (4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * 2) (Real.sqrt 8 * (Real.sqrt 8)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)))) < ((-26460296251548903/400000000000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((4133825744489791568842555101670929/50000000000000000000000000000000 : ℝ)) < ((-26460296251548903/400000000000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo8
    · exact lt_of_le_of_lt hthi8 (lt_of_lt_of_le h3i hsqX.1)
  constructor
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbrX, hEbrid8, h8, ← hEbrid]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t48 :
    ((36125921859855502849/25000000000000000000 : ℝ)) ≤ dihY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ∧ dihY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) ≤ ((289007653289092489219/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus) = deltaX (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) := by rfl
  have hE4 : deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((4092039/390625 : ℝ)) := by
    unfold deltaX4; ring
  have hE : deltaX (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((15876/390625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) = ((252047376/244140625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((1676186083635988239/244140625000000 : ℝ)) ≤ ((252047376/244140625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ∧ ((252047376/244140625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ≤ ((16369370423783641719/2384185791015625 : ℝ)) := by
    have hp0 : ((252047376/244140625 : ℝ)) ≤ ((252047376/244140625 : ℝ)) ∧ ((252047376/244140625 : ℝ)) ≤ ((252047376/244140625 : ℝ)) := by norm_num
    have hp1 : ((1676186083635988239/244140625000000 : ℝ)) ≤ ((252047376/244140625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ∧ ((252047376/244140625 : ℝ)) * (((6031/1 : ℝ)) * hminus ^ 2 + ((-2500/1 : ℝ))) ≤ ((16369370423783641719/2384185791015625 : ℝ)) := by
      have hf := ztgcTrioF_f3
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hs1 : ((8285926742720376304632572795408361/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((1676186083635988239/244140625000000 : ℝ)) := by norm_num
  have hs2 : ((16369370423783641719/2384185791015625 : ℝ)) ≤ ((4143009650180614675796501805732457/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((8285926742720376304632572795408361/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) ∧ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) ≤ ((4143009650180614675796501805732457/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((4092039/390625 : ℝ)) ≤ deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ∧ deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) ≤ ((4092039/390625 : ℝ)) := by
    rw [hE4]
    have hp0 : ((4092039/390625 : ℝ)) ≤ ((4092039/390625 : ℝ)) ∧ ((4092039/390625 : ℝ)) ≤ ((4092039/390625 : ℝ)) := by norm_num
    exact ⟨le_trans (by norm_num) hp0.1, le_trans hp0.2 (by norm_num)⟩
  have htlo : ((-4092039/390625 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) ≤ ((-4092039/390625 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| ≤ ((4092039/390625 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-4092039/390625 : ℝ)) < ((8285926742720376304632572795408361/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((8285926742720376304632572795408361/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus))))| < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) ≤ -((8285926742720376304632572795408361/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) < ((-4092039/390625 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((8285926742720376304632572795408361/100000000000000000000000000000000 : ℝ)) < ((-4092039/390625 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-4092039/390625 : ℝ)) ≤ ((-523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ)) * ((4143009650180614675796501805732457/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) ≤ ((-523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-12932864000000000000000000000000/102295391885436744501636701177881 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-12932864000000000000000000000000/102295391885436744501636701177881 : ℝ)) * ((8285926742720376304632572795408361/100000000000000000000000000000000 : ℝ)) ≤ ((-4092039/390625 : ℝ)) := by norm_num
  have harg2 : ((-12932864000000000000000000000000/102295391885436744501636701177881 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 (2 * hminus) 2 (2 * hminus) 2 (2 * hminus))) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((12932864000000000000000000000000/102295391885436744501636701177881 : ℝ))) (lo := ((12575945136067650527/100000000000000000000 : ℝ))) (hi := ((12575945140067650527/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-12932864000000000000000000000000/102295391885436744501636701177881 : ℝ)) = -Real.arctan ((12932864000000000000000000000000/102295391885436744501636701177881 : ℝ)) := by rw [show ((-12932864000000000000000000000000/102295391885436744501636701177881 : ℝ)) = -((12932864000000000000000000000000/102295391885436744501636701177881 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((12575945140067650527/100000000000000000000 : ℝ)) ≤ Real.arctan ((-12932864000000000000000000000000/102295391885436744501636701177881 : ℝ)) ∧ Real.arctan ((-12932864000000000000000000000000/102295391885436744501636701177881 : ℝ)) ≤ -((12575945136067650527/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ))) (lo := ((6287903067471708657/50000000000000000000 : ℝ))) (hi := ((6287903069471708657/50000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ)) = -Real.arctan ((523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ)) := by rw [show ((-523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ)) = -((523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((6287903069471708657/50000000000000000000 : ℝ)) ≤ Real.arctan ((-523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ)) ∧ Real.arctan ((-523780992000000000000000000000000/4143009650180614675796501805732457 : ℝ)) ≤ -((6287903067471708657/50000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t49 :
    ((804036523426103649849/500000000000000000000 : ℝ)) ≤ dihY 2.52 2 (2 * hminus) (2 * hminus) 2 2 ∧ dihY 2.52 2 (2 * hminus) (2 * hminus) 2 2 ≤ ((402020716960684629011/250000000000000000000 : ℝ)) := by
  have hEbrid : deltaY 2.52 2 (2 * hminus) (2 * hminus) 2 2 = deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) := by rfl
  have hE4 : deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-3969/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-3531/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-4/390625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) = ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((19438776052590670267779/3814697265625000000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ≤ ((49766112688034244705399/9765625000000000000 : ℝ)) := by
    have hp0 : ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) ∧ ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) := by norm_num
    have hp1 : ((19438776052590670267779/3814697265625000000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (((6250000/1 : ℝ)) * hminus ^ 4 + ((-26514539/1 : ℝ)) * hminus ^ 2 + ((6250000/1 : ℝ))) ≤ ((49766112688034244705399/9765625000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f22
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hs1 : ((892307271691819134827283081719421/12500000000000000000000000000000 : ℝ)) ^ 2 ≤ ((19438776052590670267779/3814697265625000000 : ℝ)) := by norm_num
  have hs2 : ((49766112688034244705399/9765625000000000000 : ℝ)) ≤ ((3569331148567896809611485678611163/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((892307271691819134827283081719421/12500000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) (2 * hminus) 2 2)) ∧ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) (2 * hminus) 2 2)) ≤ ((3569331148567896809611485678611163/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((-65012652621/24414062500 : ℝ)) ≤ deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) ∧ deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2) ≤ ((-6655731201/2500000000 : ℝ)) := by
    rw [hE4]
    have hp0 : ((-3969/390625 : ℝ)) ≤ ((-3969/390625 : ℝ)) ∧ ((-3969/390625 : ℝ)) ≤ ((-3969/390625 : ℝ)) := by norm_num
    have hp1 : ((-65012652621/24414062500 : ℝ)) ≤ ((-3969/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-3531/1 : ℝ))) ∧ ((-3969/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 2 + ((-3531/1 : ℝ))) ≤ ((-6655731201/2500000000 : ℝ)) := by
      have hf := ztgcTrioF_f36
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((6655731201/2500000000 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) ≤ ((65012652621/24414062500 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2)))| ≤ ((65012652621/24414062500 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((65012652621/24414062500 : ℝ)) < ((892307271691819134827283081719421/12500000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((892307271691819134827283081719421/12500000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2)))| < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) (2 * hminus) 2 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) (2 * hminus) 2 2)) ≤ -((892307271691819134827283081719421/12500000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) (2 * hminus) 2 2)) < ((6655731201/2500000000 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((892307271691819134827283081719421/12500000000000000000000000000000 : ℝ)) < ((6655731201/2500000000 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) (2 * hminus) 2 2)) := lt_of_lt_of_le h3s hsq.1
  have hthip : (0:ℝ) ≤ ((65012652621/24414062500 : ℝ)) := by norm_num
  have hnum : ((65012652621/24414062500 : ℝ)) ≤ ((3698497571328000000000000000000/99145252410202126091920342413269 : ℝ)) * ((892307271691819134827283081719421/12500000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) (2 * hminus) 2 2)) ≤ ((3698497571328000000000000000000/99145252410202126091920342413269 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hthip]
  have hnulop : (0:ℝ) ≤ ((6338791620000000000000000000000/169968149931804609981499318029103 : ℝ)) := by norm_num
  have hnum2 : ((6338791620000000000000000000000/169968149931804609981499318029103 : ℝ)) * ((3569331148567896809611485678611163/50000000000000000000000000000000 : ℝ)) ≤ ((6655731201/2500000000 : ℝ)) := by norm_num
  have harg2 : ((6338791620000000000000000000000/169968149931804609981499318029103 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * hminus * (2 * hminus)) (2 * 2) (2 * 2))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) (2 * hminus) 2 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulop]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htulo := g4v_atan_pos_bounds (x := ((6338791620000000000000000000000/169968149931804609981499318029103 : ℝ))) (lo := ((9319180264327670117/250000000000000000000 : ℝ))) (hi := ((9319180274327670117/250000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htpuhi := g4v_atan_pos_bounds (x := ((3698497571328000000000000000000/99145252410202126091920342413269 : ℝ))) (lo := ((37286540007841896809/1000000000000000000000 : ℝ))) (hi := ((37286540047841896809/1000000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t50 :
    ((111513535926234496279/100000000000000000000 : ℝ)) ≤ dihY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 ∧ dihY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 ≤ ((223032905623993037471/200000000000000000000 : ℝ)) := by
  have hEbrid : deltaY 2.52 2 (2 * hminus) 2 (2 * hminus) 2 = deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) := by rfl
  have hE4 : deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((3969/390625 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ))) := by
    unfold deltaX4; ring
  have hE : deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-15876/390625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-252047376/244140625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((209530264189605791055246/37252902984619140625 : ℝ)) ≤ ((-252047376/244140625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ∧ ((-252047376/244140625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ≤ ((8789035105494069644799/1562500000000000000 : ℝ)) := by
    have hp0 : ((-252047376/244140625 : ℝ)) ≤ ((-252047376/244140625 : ℝ)) ∧ ((-252047376/244140625 : ℝ)) ≤ ((-252047376/244140625 : ℝ)) := by norm_num
    have hp1 : ((209530264189605791055246/37252902984619140625 : ℝ)) ≤ ((-252047376/244140625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ∧ ((-252047376/244140625 : ℝ)) * (((2500/1 : ℝ)) * hminus ^ 4 + ((-10000/1 : ℝ)) * hminus ^ 2 + ((3969/1 : ℝ))) ≤ ((8789035105494069644799/1562500000000000000 : ℝ)) := by
      have hf := ztgcTrioF_f24
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have hs1 : ((7499690127834361135798721655638673/100000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((209530264189605791055246/37252902984619140625 : ℝ)) := by norm_num
  have hs2 : ((8789035105494069644799/1562500000000000000 : ℝ)) ≤ ((7499988311668436908583116683619087/100000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((7499690127834361135798721655638673/100000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) 2 (2 * hminus) 2)) ∧ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) 2 (2 * hminus) 2)) ≤ ((7499988311668436908583116683619087/100000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((45939305601/1250000000 : ℝ)) ≤ deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((448641308871/12207031250 : ℝ)) := by
    rw [hE4]
    have hp0 : ((3969/390625 : ℝ)) ≤ ((3969/390625 : ℝ)) ∧ ((3969/390625 : ℝ)) ≤ ((3969/390625 : ℝ)) := by norm_num
    have hp1 : ((45939305601/1250000000 : ℝ)) ≤ ((3969/390625 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ))) ∧ ((3969/390625 : ℝ)) * (((5000/1 : ℝ)) * hminus ^ 2 + ((-3969/1 : ℝ))) ≤ ((448641308871/12207031250 : ℝ)) := by
      have hf := ztgcTrioF_f67
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp1.1, le_trans hp1.2 (by norm_num)⟩
  have htlo : ((-448641308871/12207031250 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) ≤ ((-45939305601/1250000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)))| ≤ ((448641308871/12207031250 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-45939305601/1250000000 : ℝ)) < ((7499690127834361135798721655638673/100000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((7499690127834361135798721655638673/100000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)))| < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) 2 (2 * hminus) 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) 2 (2 * hminus) 2)) ≤ -((7499690127834361135798721655638673/100000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) 2 (2 * hminus) 2)) < ((-448641308871/12207031250 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((7499690127834361135798721655638673/100000000000000000000000000000000 : ℝ)) < ((-448641308871/12207031250 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) 2 (2 * hminus) 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-45939305601/1250000000 : ℝ)) ≤ ((-525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ)) * ((7499988311668436908583116683619087/100000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) 2 (2 * hminus) 2)) ≤ ((-525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-408363289141248000000000000000000/833298903092706792866524628404297 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-408363289141248000000000000000000/833298903092706792866524628404297 : ℝ)) * ((7499690127834361135798721655638673/100000000000000000000000000000000 : ℝ)) ≤ ((-448641308871/12207031250 : ℝ)) := by norm_num
  have harg2 : ((-408363289141248000000000000000000/833298903092706792866524628404297 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 (2 * hminus) 2 (2 * hminus) 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((408363289141248000000000000000000/833298903092706792866524628404297 : ℝ))) (lo := ((11391524162313791411/25000000000000000000 : ℝ))) (hi := ((11391524163313791411/25000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-408363289141248000000000000000000/833298903092706792866524628404297 : ℝ)) = -Real.arctan ((408363289141248000000000000000000/833298903092706792866524628404297 : ℝ)) := by rw [show ((-408363289141248000000000000000000/833298903092706792866524628404297 : ℝ)) = -((408363289141248000000000000000000/833298903092706792866524628404297 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((11391524163313791411/25000000000000000000 : ℝ)) ≤ Real.arctan ((-408363289141248000000000000000000/833298903092706792866524628404297 : ℝ)) ∧ Real.arctan ((-408363289141248000000000000000000/833298903092706792866524628404297 : ℝ)) ≤ -((11391524162313791411/25000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ))) (lo := ((11390794991873285797/25000000000000000000 : ℝ))) (hi := ((11390794992873285797/25000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ)) = -Real.arctan ((525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ)) := by rw [show ((-525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ)) = -((525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((11390794992873285797/25000000000000000000 : ℝ)) ≤ Real.arctan ((-525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ)) ∧ Real.arctan ((-525020635440000000000000000000000/1071426901666919558369016669088441 : ℝ)) ≤ -((11390794991873285797/25000000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

theorem ztgcTrioT_t51 :
    ((2747390430343595661/2500000000000000000 : ℝ)) ≤ dihY 2.52 2 2.52 2 (2 * hminus) 2 ∧ dihY 2.52 2 2.52 2 (2 * hminus) 2 ≤ ((8791745527868926831/8000000000000000000 : ℝ)) := by
  have hEbrid : deltaY 2.52 2 2.52 2 (2 * hminus) 2 = deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) := by rfl
  have hE4 : deltaX4 (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((15876/625 : ℝ)) * (hminus) * (hminus) := by
    unfold deltaX4; ring
  have hE : deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-4/390625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) := by
    unfold deltaX; ring
  have hEA : 4 * (2.52 * 2.52) * deltaX (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) = ((-63504/244140625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) := by
    rw [hE]; ring
  have hA : ((17408218998170765583/3051757812500000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ≤ ((870434354758198699791/152587890625000000 : ℝ)) := by
    have hp0 : ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) ∧ ((-63504/244140625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) := by norm_num
    have hp1 : ((-244442772/762939453125 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (hminus) ∧ ((-63504/244140625 : ℝ)) * (hminus) ≤ ((-19555263/61035156250 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((-940921340121/2384185791015625 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (hminus) * (hminus) ∧ ((-63504/244140625 : ℝ)) * (hminus) * (hminus) ≤ ((-96348780801/244140625000000 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    have hp3 : ((17408218998170765583/3051757812500000 : ℝ)) ≤ ((-63504/244140625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ∧ ((-63504/244140625 : ℝ)) * (hminus) * (hminus) * (((6250000/1 : ℝ)) * hminus ^ 2 + ((-23937039/1 : ℝ))) ≤ ((870434354758198699791/152587890625000000 : ℝ)) := by
      have hf := ztgcTrioF_f38
      constructor <;> nlinarith [hp2.1, hp2.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp3.1, le_trans hp3.2 (by norm_num)⟩
  have hs1 : ((3776349163319144930208366808173063/50000000000000000000000000000000 : ℝ)) ^ 2 ≤ ((17408218998170765583/3051757812500000 : ℝ)) := by norm_num
  have hs2 : ((870434354758198699791/152587890625000000 : ℝ)) ≤ ((3776399934906075691699349060379277/50000000000000000000000000000000 : ℝ)) ^ 2 := by norm_num
  have hsq : ((3776349163319144930208366808173063/50000000000000000000000000000000 : ℝ)) ≤ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 2.52 2 (2 * hminus) 2)) ∧ (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 2.52 2 (2 * hminus) 2)) ≤ ((3776399934906075691699349060379277/50000000000000000000000000000000 : ℝ)) := by
    rw [hEbrid, hEA]
    exact ztg_sqrt_bounds (by norm_num) (by norm_num) (by linarith [hs1, hA.1]) (by linarith [hA.2, hs2])
  have h4 : ((96348780801/2500000000 : ℝ)) ≤ deltaX4 (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ∧ deltaX4 (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2) ≤ ((940921340121/24414062500 : ℝ)) := by
    rw [hE4]
    have hp0 : ((15876/625 : ℝ)) ≤ ((15876/625 : ℝ)) ∧ ((15876/625 : ℝ)) ≤ ((15876/625 : ℝ)) := by norm_num
    have hp1 : ((19555263/625000 : ℝ)) ≤ ((15876/625 : ℝ)) * (hminus) ∧ ((15876/625 : ℝ)) * (hminus) ≤ ((61110693/1953125 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp0.1, hp0.2, hf.1, hf.2]
    have hp2 : ((96348780801/2500000000 : ℝ)) ≤ ((15876/625 : ℝ)) * (hminus) * (hminus) ∧ ((15876/625 : ℝ)) * (hminus) * (hminus) ≤ ((940921340121/24414062500 : ℝ)) := by
      have hf := ztgcTrioF_f0
      constructor <;> nlinarith [hp1.1, hp1.2, hf.1, hf.2]
    exact ⟨le_trans (by norm_num) hp2.1, le_trans hp2.2 (by norm_num)⟩
  have htlo : ((-940921340121/24414062500 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) := by rw [hE4]; linarith [h4.2]
  have hthi : (-(deltaX4 (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) ≤ ((-96348780801/2500000000 : ℝ)) := by rw [hE4]; linarith [h4.1]
  have habsu : |(-(deltaX4 (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)))| ≤ ((940921340121/24414062500 : ℝ)) := by
    rw [abs_le]
    constructor <;> linarith [htlo, hthi]
  have h3i : ((-96348780801/2500000000 : ℝ)) < ((3776349163319144930208366808173063/50000000000000000000000000000000 : ℝ)) := by norm_num
  have h3s : (0:ℝ) < ((3776349163319144930208366808173063/50000000000000000000000000000000 : ℝ)) := by norm_num
  have hbr : |(-(deltaX4 (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2)))| < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 2.52 2 (2 * hminus) 2)) := by
    rw [abs_lt]
    have hn : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 2.52 2 (2 * hminus) 2)) ≤ -((3776349163319144930208366808173063/50000000000000000000000000000000 : ℝ)) := neg_le_neg hsq.1
    have h1 : -(Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 2.52 2 (2 * hminus) 2)) < ((-940921340121/24414062500 : ℝ)) :=
      lt_of_le_of_lt hn (by norm_num :
        -((3776349163319144930208366808173063/50000000000000000000000000000000 : ℝ)) < ((-940921340121/24414062500 : ℝ)))
    constructor
    · exact lt_of_lt_of_le h1 htlo
    · exact lt_of_le_of_lt hthi (lt_of_lt_of_le h3i hsq.1)
  have hsqpos : (0:ℝ) < (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 2.52 2 (2 * hminus) 2)) := lt_of_lt_of_le h3s hsq.1
  have hnugi : ((-1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ)) ≤ 0 := by norm_num
  have hnum : ((-96348780801/2500000000 : ℝ)) ≤ ((-1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ)) * ((3776399934906075691699349060379277/50000000000000000000000000000000 : ℝ)) := by norm_num
  have harg : (-(deltaX4 (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 2.52 2 (2 * hminus) 2)) ≤ ((-1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ)) := by
    rw [div_le_iff₀ hsqpos]
    nlinarith [hthi, hsqpos, hnum, hnugi]
  have hnulol : ((-214111878285312000000000000000000/419594351479904992245374089797007 : ℝ)) ≤ 0 := by norm_num
  have hnum2 : ((-214111878285312000000000000000000/419594351479904992245374089797007 : ℝ)) * ((3776349163319144930208366808173063/50000000000000000000000000000000 : ℝ)) ≤ ((-940921340121/24414062500 : ℝ)) := by norm_num
  have harg2 : ((-214111878285312000000000000000000/419594351479904992245374089797007 : ℝ)) ≤ (-(deltaX4 (2.52 * 2.52) (2 * 2) (2.52 * 2.52) (2 * 2) (2 * hminus * (2 * hminus)) (2 * 2))) / (Real.sqrt (4 * (2.52 * 2.52) * deltaY 2.52 2 2.52 2 (2 * hminus) 2)) := by
    rw [le_div_iff₀ hsqpos]
    nlinarith [htlo, hsqpos, hnum2, hnulol]
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have htplo := g4v_atan_pos_bounds (x := ((214111878285312000000000000000000/419594351479904992245374089797007 : ℝ))) (lo := ((47184015361745835483/100000000000000000000 : ℝ))) (hi := ((47184015365745835483/100000000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnglo : Real.arctan ((-214111878285312000000000000000000/419594351479904992245374089797007 : ℝ)) = -Real.arctan ((214111878285312000000000000000000/419594351479904992245374089797007 : ℝ)) := by rw [show ((-214111878285312000000000000000000/419594351479904992245374089797007 : ℝ)) = -((214111878285312000000000000000000/419594351479904992245374089797007 : ℝ)) from by norm_num, Real.arctan_neg]
  have htulo : -((47184015365745835483/100000000000000000000 : ℝ)) ≤ Real.arctan ((-214111878285312000000000000000000/419594351479904992245374089797007 : ℝ)) ∧ Real.arctan ((-214111878285312000000000000000000/419594351479904992245374089797007 : ℝ)) ≤ -((47184015361745835483/100000000000000000000 : ℝ)) := by
    rw [hnglo]
    constructor <;> linarith [htplo.1, htplo.2]
  have htphi := g4v_atan_pos_bounds (x := ((1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ))) (lo := ((5897851710141009567/12500000000000000000 : ℝ))) (hi := ((5897851710641009567/12500000000000000000 : ℝ))) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnghi : Real.arctan ((-1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ)) = -Real.arctan ((1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ)) := by rw [show ((-1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ)) = -((1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ)) from by norm_num, Real.arctan_neg]
  have htpuhi : -((5897851710641009567/12500000000000000000 : ℝ)) ≤ Real.arctan ((-1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ)) ∧ Real.arctan ((-1926975616020000000000000000000000/3776399934906075691699349060379277 : ℝ)) ≤ -((5897851710141009567/12500000000000000000 : ℝ)) := by
    rw [hnghi]
    constructor <;> linarith [htphi.1, htphi.2]
  have hmono := Real.arctan_mono harg2
  have hmono' := Real.arctan_mono harg
  constructor
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [htulo.1, hmono, hp1]
  · rw [ztg_dihY_eq_br1 hbr]
    linarith [hmono', htpuhi.2, hp2]

/-! ## Axiom audit -/

#print axioms ztgcTrioT_t0
#print axioms ztgcTrioT_t1
#print axioms ztgcTrioT_t2
#print axioms ztgcTrioT_t3
#print axioms ztgcTrioT_t4
#print axioms ztgcTrioT_t5
#print axioms ztgcTrioT_t6
#print axioms ztgcTrioT_t7
#print axioms ztgcTrioT_t8
#print axioms ztgcTrioT_t9
#print axioms ztgcTrioT_t10
#print axioms ztgcTrioT_t11
#print axioms ztgcTrioT_t12
#print axioms ztgcTrioT_t13
#print axioms ztgcTrioT_t14
#print axioms ztgcTrioT_t15
#print axioms ztgcTrioT_t16
#print axioms ztgcTrioT_t17
#print axioms ztgcTrioT_t18
#print axioms ztgcTrioT_t19
#print axioms ztgcTrioT_t20
#print axioms ztgcTrioT_t21
#print axioms ztgcTrioT_t22
#print axioms ztgcTrioT_t23
#print axioms ztgcTrioT_t24
#print axioms ztgcTrioT_t25
#print axioms ztgcTrioT_t26
#print axioms ztgcTrioT_t27
#print axioms ztgcTrioT_t28
#print axioms ztgcTrioT_t29
#print axioms ztgcTrioT_t30
#print axioms ztgcTrioT_t31
#print axioms ztgcTrioT_t32
#print axioms ztgcTrioT_t33
#print axioms ztgcTrioT_t34
#print axioms ztgcTrioT_t35
#print axioms ztgcTrioT_t36
#print axioms ztgcTrioT_t37
#print axioms ztgcTrioT_t38
#print axioms ztgcTrioT_t39
#print axioms ztgcTrioT_t40
#print axioms ztgcTrioT_t41
#print axioms ztgcTrioT_t42
#print axioms ztgcTrioT_t43
#print axioms ztgcTrioT_t44
#print axioms ztgcTrioT_t45
#print axioms ztgcTrioT_t46
#print axioms ztgcTrioT_t47
#print axioms ztgcTrioT_t48
#print axioms ztgcTrioT_t49
#print axioms ztgcTrioT_t50
#print axioms ztgcTrioT_t51

end Kepler.Text
