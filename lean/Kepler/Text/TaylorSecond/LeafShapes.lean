/- LeafShapes — lane wt1-full-emission-w1 (generated).
   One ℝ shape lemma per `Wt1TowerDeriv` slot definition: rewrites the
   slot def into the exact op tree the generated `QInterval` mem chains
   consume, so each per-box membership proof is a pure `QInterval.mem_*`
   composition. -/
import Kepler.Text.TaylorSecond.LeafChain

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

/-- `w1aA y4 y5 y6` shape. -/
theorem sh_aA (y4 y5 y6 : ℝ) :
    w1aA y4 y5 y6 = ((((((Real.sqrt 2) * y5) * y4) + ((y5 * (y4 * y4)) * ((2:ℝ))⁻¹)) + (((Real.sqrt 2) * (((y5 * y5) + (y4 * y4)) - (y6 * y6))) * ((2:ℝ))⁻¹)) + ((y4 * (y5 * y5)) * ((2:ℝ))⁻¹)) := by
  unfold w1aA
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1aB y4 y5 y6` shape. -/
theorem sh_aB (y4 y5 y6 : ℝ) :
    w1aB y4 y5 y6 = ((((((Real.sqrt 2) * y6) * y5) + ((y6 * (y5 * y5)) * ((2:ℝ))⁻¹)) + (((Real.sqrt 2) * (((y6 * y6) + (y5 * y5)) - (y4 * y4))) * ((2:ℝ))⁻¹)) + ((y5 * (y6 * y6)) * ((2:ℝ))⁻¹)) := by
  unfold w1aB
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1aC y4 y5 y6` shape. -/
theorem sh_aC (y4 y5 y6 : ℝ) :
    w1aC y4 y5 y6 = ((((((Real.sqrt 2) * y4) * y6) + ((y4 * (y6 * y6)) * ((2:ℝ))⁻¹)) + (((Real.sqrt 2) * (((y4 * y4) + (y6 * y6)) - (y5 * y5))) * ((2:ℝ))⁻¹)) + ((y6 * (y4 * y4)) * ((2:ℝ))⁻¹)) := by
  unfold w1aC
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1aAD y4 y5 y6` shape. -/
theorem sh_aAD (y4 y5 y6 : ℝ) :
    w1aAD y4 y5 y6 = ((((Real.sqrt 2) + y4) * y5) + (((Real.sqrt 2) * y4) + ((y4 * y4) * ((2:ℝ))⁻¹))) := by
  unfold w1aAD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1aBD y4 y5 y6` shape. -/
theorem sh_aBD (y4 y5 y6 : ℝ) :
    w1aBD y4 y5 y6 = ((((Real.sqrt 2) + y6) * y5) + (((Real.sqrt 2) * y6) + ((y6 * y6) * ((2:ℝ))⁻¹))) := by
  unfold w1aBD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1aCD y4 y5 y6` shape. -/
theorem sh_aCD (y4 y5 y6 : ℝ) :
    w1aCD y4 y5 y6 = ((-(Real.sqrt 2)) * y5) := by
  unfold w1aCD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1aADD y4 y5 y6` shape. -/
theorem sh_aADD (y4 y5 y6 : ℝ) :
    w1aADD y4 y5 y6 = ((Real.sqrt 2) + y4) := by
  unfold w1aADD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1aBDD y4 y5 y6` shape. -/
theorem sh_aBDD (y4 y5 y6 : ℝ) :
    w1aBDD y4 y5 y6 = ((Real.sqrt 2) + y6) := by
  unfold w1aBDD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1aCDD y4 y5 y6` shape. -/
theorem sh_aCDD (y4 y5 y6 : ℝ) :
    w1aCDD y4 y5 y6 = (-(Real.sqrt 2)) := by
  unfold w1aCDD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1d4A y4 y5 y6` shape. -/
theorem sh_d4A (y4 y5 y6 : ℝ) :
    w1d4A y4 y5 y6 = ((y5 * y5) * (((y4 * y4) + (y6 * y6)) - (y5 * y5))) := by
  unfold w1d4A
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1d4B y4 y5 y6` shape. -/
theorem sh_d4B (y4 y5 y6 : ℝ) :
    w1d4B y4 y5 y6 = ((y6 * y6) * (((y5 * y5) + (y4 * y4)) - (y6 * y6))) := by
  unfold w1d4B
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1d4C y4 y5 y6` shape. -/
theorem sh_d4C (y4 y5 y6 : ℝ) :
    w1d4C y4 y5 y6 = ((y4 * y4) * (((y6 * y6) + (y5 * y5)) - (y4 * y4))) := by
  unfold w1d4C
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1d4AD y4 y5 y6` shape. -/
theorem sh_d4AD (y4 y5 y6 : ℝ) :
    w1d4AD y4 y5 y6 = ((((2:ℝ) * ((y4 * y4) + (y6 * y6))) * y5) - (((y5 * y5) * y5) * (4:ℝ))) := by
  unfold w1d4AD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1d4BD y4 y5 y6` shape. -/
theorem sh_d4BD (y4 y5 y6 : ℝ) :
    w1d4BD y4 y5 y6 = (((2:ℝ) * (y6 * y6)) * y5) := by
  unfold w1d4BD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1d4CD y4 y5 y6` shape. -/
theorem sh_d4CD (y4 y5 y6 : ℝ) :
    w1d4CD y4 y5 y6 = (((2:ℝ) * (y4 * y4)) * y5) := by
  unfold w1d4CD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1d4ADD y4 y5 y6` shape. -/
theorem sh_d4ADD (y4 y5 y6 : ℝ) :
    w1d4ADD y4 y5 y6 = (((2:ℝ) * ((y4 * y4) + (y6 * y6))) - ((12:ℝ) * (y5 * y5))) := by
  unfold w1d4ADD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1d4BDD y4 y5 y6` shape. -/
theorem sh_d4BDD (y4 y5 y6 : ℝ) :
    w1d4BDD y4 y5 y6 = ((2:ℝ) * (y6 * y6)) := by
  unfold w1d4BDD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1d4CDD y4 y5 y6` shape. -/
theorem sh_d4CDD (y4 y5 y6 : ℝ) :
    w1d4CDD y4 y5 y6 = ((2:ℝ) * (y4 * y4)) := by
  unfold w1d4CDD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1DltD y4 y5 y6` shape. -/
theorem sh_DltD (y4 y5 y6 : ℝ) :
    w1DltD y4 y5 y6 = (((2:ℝ) * y5) * (((((4:ℝ) * (y4 * y4)) + ((4:ℝ) * (y6 * y6))) - ((4:ℝ) * (y5 * y5))) - ((y4 * y4) * (y6 * y6)))) := by
  unfold w1DltD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1DltDD y4 y5 y6` shape. -/
theorem sh_DltDD (y4 y5 y6 : ℝ) :
    w1DltDD y4 y5 y6 = (((((8:ℝ) * (y4 * y4)) + ((8:ℝ) * (y6 * y6))) - (((4:ℝ) * (y5 * y5)) * (6:ℝ))) - ((2:ℝ) * ((y4 * y4) * (y6 * y6)))) := by
  unfold w1DltDD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1tA y4 y5 y6` shape. -/
theorem sh_tA (y4 y5 y6 : ℝ) :
    w1tA y4 y5 y6 = ((w1Dlt y4 y5 y6) * (((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6)))⁻¹) := by
  unfold w1tA w1tOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1tAD y4 y5 y6` shape. -/
theorem sh_tAD (y4 y5 y6 : ℝ) (hA : w1aA y4 y5 y6 ≠ 0) :
    w1tAD y4 y5 y6 = (((w1DltD y4 y5 y6 * ((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6))) - ((w1Dlt y4 y5 y6) * (((8:ℝ) * w1aA y4 y5 y6) * w1aAD y4 y5 y6))) * ((((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6)) * ((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6))))⁻¹) := by
  unfold w1tAD w1tDfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try field_simp
  try ring

/-- `w1tADD y4 y5 y6` shape. -/
theorem sh_tADD (y4 y5 y6 : ℝ) (hA : w1aA y4 y5 y6 ≠ 0) :
    w1tADD y4 y5 y6 = ((((((w1DltDD y4 y5 y6 * ((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6))) - (((8:ℝ) * (w1Dlt y4 y5 y6)) * (w1aAD y4 y5 y6 * w1aAD y4 y5 y6))) - ((((8:ℝ) * (w1Dlt y4 y5 y6)) * w1aA y4 y5 y6) * w1aADD y4 y5 y6)) * (((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6)) * ((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6)))) - (((w1DltD y4 y5 y6 * ((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6))) - ((w1Dlt y4 y5 y6) * (((8:ℝ) * w1aA y4 y5 y6) * w1aAD y4 y5 y6))) * (((2:ℝ) * ((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6))) * (((8:ℝ) * w1aA y4 y5 y6) * w1aAD y4 y5 y6)))) * (((((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6)) * ((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6))) * (((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6)) * ((4:ℝ) * (w1aA y4 y5 y6 * w1aA y4 y5 y6)))))⁻¹) := by
  unfold w1tADD w1tDDOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try field_simp
  try ring

/-- `w1tB y4 y5 y6` shape. -/
theorem sh_tB (y4 y5 y6 : ℝ) :
    w1tB y4 y5 y6 = ((w1Dlt y4 y5 y6) * (((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6)))⁻¹) := by
  unfold w1tB w1tOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1tBD y4 y5 y6` shape. -/
theorem sh_tBD (y4 y5 y6 : ℝ) (hA : w1aB y4 y5 y6 ≠ 0) :
    w1tBD y4 y5 y6 = (((w1DltD y4 y5 y6 * ((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6))) - ((w1Dlt y4 y5 y6) * (((8:ℝ) * w1aB y4 y5 y6) * w1aBD y4 y5 y6))) * ((((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6)) * ((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6))))⁻¹) := by
  unfold w1tBD w1tDfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try field_simp
  try ring

/-- `w1tBDD y4 y5 y6` shape. -/
theorem sh_tBDD (y4 y5 y6 : ℝ) (hA : w1aB y4 y5 y6 ≠ 0) :
    w1tBDD y4 y5 y6 = ((((((w1DltDD y4 y5 y6 * ((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6))) - (((8:ℝ) * (w1Dlt y4 y5 y6)) * (w1aBD y4 y5 y6 * w1aBD y4 y5 y6))) - ((((8:ℝ) * (w1Dlt y4 y5 y6)) * w1aB y4 y5 y6) * w1aBDD y4 y5 y6)) * (((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6)) * ((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6)))) - (((w1DltD y4 y5 y6 * ((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6))) - ((w1Dlt y4 y5 y6) * (((8:ℝ) * w1aB y4 y5 y6) * w1aBD y4 y5 y6))) * (((2:ℝ) * ((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6))) * (((8:ℝ) * w1aB y4 y5 y6) * w1aBD y4 y5 y6)))) * (((((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6)) * ((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6))) * (((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6)) * ((4:ℝ) * (w1aB y4 y5 y6 * w1aB y4 y5 y6)))))⁻¹) := by
  unfold w1tBDD w1tDDOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try field_simp
  try ring

/-- `w1tC y4 y5 y6` shape. -/
theorem sh_tC (y4 y5 y6 : ℝ) :
    w1tC y4 y5 y6 = ((w1Dlt y4 y5 y6) * (((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6)))⁻¹) := by
  unfold w1tC w1tOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1tCD y4 y5 y6` shape. -/
theorem sh_tCD (y4 y5 y6 : ℝ) (hA : w1aC y4 y5 y6 ≠ 0) :
    w1tCD y4 y5 y6 = (((w1DltD y4 y5 y6 * ((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6))) - ((w1Dlt y4 y5 y6) * (((8:ℝ) * w1aC y4 y5 y6) * w1aCD y4 y5 y6))) * ((((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6)) * ((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6))))⁻¹) := by
  unfold w1tCD w1tDfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try field_simp
  try ring

/-- `w1tCDD y4 y5 y6` shape. -/
theorem sh_tCDD (y4 y5 y6 : ℝ) (hA : w1aC y4 y5 y6 ≠ 0) :
    w1tCDD y4 y5 y6 = ((((((w1DltDD y4 y5 y6 * ((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6))) - (((8:ℝ) * (w1Dlt y4 y5 y6)) * (w1aCD y4 y5 y6 * w1aCD y4 y5 y6))) - ((((8:ℝ) * (w1Dlt y4 y5 y6)) * w1aC y4 y5 y6) * w1aCDD y4 y5 y6)) * (((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6)) * ((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6)))) - (((w1DltD y4 y5 y6 * ((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6))) - ((w1Dlt y4 y5 y6) * (((8:ℝ) * w1aC y4 y5 y6) * w1aCD y4 y5 y6))) * (((2:ℝ) * ((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6))) * (((8:ℝ) * w1aC y4 y5 y6) * w1aCD y4 y5 y6)))) * (((((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6)) * ((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6))) * (((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6)) * ((4:ℝ) * (w1aC y4 y5 y6 * w1aC y4 y5 y6)))))⁻¹) := by
  unfold w1tCDD w1tDDOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try field_simp
  try ring

/-- `w1gA y4 y5 y6` shape. -/
theorem sh_gA (y4 y5 y6 : ℝ) :
    w1gA y4 y5 y6 = ((((4:ℝ) * (y5 * y5)) * (w1Dlt y4 y5 y6)) * ((w1d4A y4 y5 y6 * w1d4A y4 y5 y6))⁻¹) := by
  unfold w1gA w1gOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1gAD y4 y5 y6` shape. -/
theorem sh_gAD (y4 y5 y6 : ℝ) :
    w1gAD y4 y5 y6 = (((((((8:ℝ) * y5) * (w1Dlt y4 y5 y6)) + (((4:ℝ) * (y5 * y5)) * w1DltD y4 y5 y6)) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6)) - ((((2:ℝ) * ((4:ℝ) * (y5 * y5))) * (w1Dlt y4 y5 y6)) * (w1d4A y4 y5 y6 * w1d4AD y4 y5 y6))) * (((w1d4A y4 y5 y6 * w1d4A y4 y5 y6) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6)))⁻¹) := by
  unfold w1gAD w1gDfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1gADD y4 y5 y6` shape. -/
theorem sh_gADD (y4 y5 y6 : ℝ) :
    w1gADD y4 y5 y6 = (((((((((8 : ℝ) * (w1Dlt y4 y5 y6)) + (((2:ℝ) * ((8:ℝ) * y5)) * w1DltD y4 y5 y6)) + (((4:ℝ) * (y5 * y5)) * w1DltDD y4 y5 y6)) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6)) - ((((2:ℝ) * ((4:ℝ) * (y5 * y5))) * (w1Dlt y4 y5 y6)) * ((w1d4AD y4 y5 y6 * w1d4AD y4 y5 y6) + (w1d4A y4 y5 y6 * w1d4ADD y4 y5 y6)))) * ((w1d4A y4 y5 y6 * w1d4A y4 y5 y6) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6))) - (((((((8:ℝ) * y5) * (w1Dlt y4 y5 y6)) + (((4:ℝ) * (y5 * y5)) * w1DltD y4 y5 y6)) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6)) - ((((2:ℝ) * ((4:ℝ) * (y5 * y5))) * (w1Dlt y4 y5 y6)) * (w1d4A y4 y5 y6 * w1d4AD y4 y5 y6))) * (((2:ℝ) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6)) * ((2:ℝ) * (w1d4A y4 y5 y6 * w1d4AD y4 y5 y6))))) * ((((w1d4A y4 y5 y6 * w1d4A y4 y5 y6) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6)) * ((w1d4A y4 y5 y6 * w1d4A y4 y5 y6) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6))))⁻¹) := by
  unfold w1gADD w1gDDOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1gB y4 y5 y6` shape. -/
theorem sh_gB (y4 y5 y6 : ℝ) :
    w1gB y4 y5 y6 = ((((4:ℝ) * (y6 * y6)) * (w1Dlt y4 y5 y6)) * ((w1d4B y4 y5 y6 * w1d4B y4 y5 y6))⁻¹) := by
  unfold w1gB w1gOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1gBD y4 y5 y6` shape. -/
theorem sh_gBD (y4 y5 y6 : ℝ) :
    w1gBD y4 y5 y6 = ((((((0 : ℝ) * (w1Dlt y4 y5 y6)) + (((4:ℝ) * (y6 * y6)) * w1DltD y4 y5 y6)) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6)) - ((((2:ℝ) * ((4:ℝ) * (y6 * y6))) * (w1Dlt y4 y5 y6)) * (w1d4B y4 y5 y6 * w1d4BD y4 y5 y6))) * (((w1d4B y4 y5 y6 * w1d4B y4 y5 y6) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6)))⁻¹) := by
  unfold w1gBD w1gDfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1gBDD y4 y5 y6` shape. -/
theorem sh_gBDD (y4 y5 y6 : ℝ) :
    w1gBDD y4 y5 y6 = (((((((((0 : ℝ) * (w1Dlt y4 y5 y6)) + (((2:ℝ) * (0 : ℝ)) * w1DltD y4 y5 y6)) + (((4:ℝ) * (y6 * y6)) * w1DltDD y4 y5 y6)) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6)) - ((((2:ℝ) * ((4:ℝ) * (y6 * y6))) * (w1Dlt y4 y5 y6)) * ((w1d4BD y4 y5 y6 * w1d4BD y4 y5 y6) + (w1d4B y4 y5 y6 * w1d4BDD y4 y5 y6)))) * ((w1d4B y4 y5 y6 * w1d4B y4 y5 y6) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6))) - ((((((0 : ℝ) * (w1Dlt y4 y5 y6)) + (((4:ℝ) * (y6 * y6)) * w1DltD y4 y5 y6)) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6)) - ((((2:ℝ) * ((4:ℝ) * (y6 * y6))) * (w1Dlt y4 y5 y6)) * (w1d4B y4 y5 y6 * w1d4BD y4 y5 y6))) * (((2:ℝ) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6)) * ((2:ℝ) * (w1d4B y4 y5 y6 * w1d4BD y4 y5 y6))))) * ((((w1d4B y4 y5 y6 * w1d4B y4 y5 y6) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6)) * ((w1d4B y4 y5 y6 * w1d4B y4 y5 y6) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6))))⁻¹) := by
  unfold w1gBDD w1gDDOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1gC y4 y5 y6` shape. -/
theorem sh_gC (y4 y5 y6 : ℝ) :
    w1gC y4 y5 y6 = ((((4:ℝ) * (y4 * y4)) * (w1Dlt y4 y5 y6)) * ((w1d4C y4 y5 y6 * w1d4C y4 y5 y6))⁻¹) := by
  unfold w1gC w1gOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1gCD y4 y5 y6` shape. -/
theorem sh_gCD (y4 y5 y6 : ℝ) :
    w1gCD y4 y5 y6 = ((((((0 : ℝ) * (w1Dlt y4 y5 y6)) + (((4:ℝ) * (y4 * y4)) * w1DltD y4 y5 y6)) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6)) - ((((2:ℝ) * ((4:ℝ) * (y4 * y4))) * (w1Dlt y4 y5 y6)) * (w1d4C y4 y5 y6 * w1d4CD y4 y5 y6))) * (((w1d4C y4 y5 y6 * w1d4C y4 y5 y6) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6)))⁻¹) := by
  unfold w1gCD w1gDfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1gCDD y4 y5 y6` shape. -/
theorem sh_gCDD (y4 y5 y6 : ℝ) :
    w1gCDD y4 y5 y6 = (((((((((0 : ℝ) * (w1Dlt y4 y5 y6)) + (((2:ℝ) * (0 : ℝ)) * w1DltD y4 y5 y6)) + (((4:ℝ) * (y4 * y4)) * w1DltDD y4 y5 y6)) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6)) - ((((2:ℝ) * ((4:ℝ) * (y4 * y4))) * (w1Dlt y4 y5 y6)) * ((w1d4CD y4 y5 y6 * w1d4CD y4 y5 y6) + (w1d4C y4 y5 y6 * w1d4CDD y4 y5 y6)))) * ((w1d4C y4 y5 y6 * w1d4C y4 y5 y6) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6))) - ((((((0 : ℝ) * (w1Dlt y4 y5 y6)) + (((4:ℝ) * (y4 * y4)) * w1DltD y4 y5 y6)) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6)) - ((((2:ℝ) * ((4:ℝ) * (y4 * y4))) * (w1Dlt y4 y5 y6)) * (w1d4C y4 y5 y6 * w1d4CD y4 y5 y6))) * (((2:ℝ) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6)) * ((2:ℝ) * (w1d4C y4 y5 y6 * w1d4CD y4 y5 y6))))) * ((((w1d4C y4 y5 y6 * w1d4C y4 y5 y6) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6)) * ((w1d4C y4 y5 y6 * w1d4C y4 y5 y6) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6))))⁻¹) := by
  unfold w1gCDD w1gDDOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1WA y4 y5 y6` shape. -/
theorem sh_WA (y4 y5 y6 : ℝ) :
    w1WA y4 y5 y6 = (((2:ℝ) * y5) * (w1d4A y4 y5 y6)⁻¹) := by
  unfold w1WA w1WOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1WAD y4 y5 y6` shape. -/
theorem sh_WAD (y4 y5 y6 : ℝ) :
    w1WAD y4 y5 y6 = ((((2 : ℝ) * w1d4A y4 y5 y6) - (((2:ℝ) * y5) * w1d4AD y4 y5 y6)) * ((w1d4A y4 y5 y6 * w1d4A y4 y5 y6))⁻¹) := by
  unfold w1WAD w1WDfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1WADD y4 y5 y6` shape. -/
theorem sh_WADD (y4 y5 y6 : ℝ) :
    w1WADD y4 y5 y6 = ((((((0:ℝ) * w1d4A y4 y5 y6) - (((2:ℝ) * y5) * w1d4ADD y4 y5 y6)) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6)) - ((((2 : ℝ) * w1d4A y4 y5 y6) - (((2:ℝ) * y5) * w1d4AD y4 y5 y6)) * ((2:ℝ) * (w1d4A y4 y5 y6 * w1d4AD y4 y5 y6)))) * (((w1d4A y4 y5 y6 * w1d4A y4 y5 y6) * (w1d4A y4 y5 y6 * w1d4A y4 y5 y6)))⁻¹) := by
  unfold w1WADD w1WDDOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1WB y4 y5 y6` shape. -/
theorem sh_WB (y4 y5 y6 : ℝ) :
    w1WB y4 y5 y6 = (((2:ℝ) * y6) * (w1d4B y4 y5 y6)⁻¹) := by
  unfold w1WB w1WOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1WBD y4 y5 y6` shape. -/
theorem sh_WBD (y4 y5 y6 : ℝ) :
    w1WBD y4 y5 y6 = ((((0 : ℝ) * w1d4B y4 y5 y6) - (((2:ℝ) * y6) * w1d4BD y4 y5 y6)) * ((w1d4B y4 y5 y6 * w1d4B y4 y5 y6))⁻¹) := by
  unfold w1WBD w1WDfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1WBDD y4 y5 y6` shape. -/
theorem sh_WBDD (y4 y5 y6 : ℝ) :
    w1WBDD y4 y5 y6 = ((((((0:ℝ) * w1d4B y4 y5 y6) - (((2:ℝ) * y6) * w1d4BDD y4 y5 y6)) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6)) - ((((0 : ℝ) * w1d4B y4 y5 y6) - (((2:ℝ) * y6) * w1d4BD y4 y5 y6)) * ((2:ℝ) * (w1d4B y4 y5 y6 * w1d4BD y4 y5 y6)))) * (((w1d4B y4 y5 y6 * w1d4B y4 y5 y6) * (w1d4B y4 y5 y6 * w1d4B y4 y5 y6)))⁻¹) := by
  unfold w1WBDD w1WDDOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1WC y4 y5 y6` shape. -/
theorem sh_WC (y4 y5 y6 : ℝ) :
    w1WC y4 y5 y6 = (((2:ℝ) * y4) * (w1d4C y4 y5 y6)⁻¹) := by
  unfold w1WC w1WOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1WCD y4 y5 y6` shape. -/
theorem sh_WCD (y4 y5 y6 : ℝ) :
    w1WCD y4 y5 y6 = ((((0 : ℝ) * w1d4C y4 y5 y6) - (((2:ℝ) * y4) * w1d4CD y4 y5 y6)) * ((w1d4C y4 y5 y6 * w1d4C y4 y5 y6))⁻¹) := by
  unfold w1WCD w1WDfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1WCDD y4 y5 y6` shape. -/
theorem sh_WCDD (y4 y5 y6 : ℝ) :
    w1WCDD y4 y5 y6 = ((((((0:ℝ) * w1d4C y4 y5 y6) - (((2:ℝ) * y4) * w1d4CDD y4 y5 y6)) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6)) - ((((0 : ℝ) * w1d4C y4 y5 y6) - (((2:ℝ) * y4) * w1d4CD y4 y5 y6)) * ((2:ℝ) * (w1d4C y4 y5 y6 * w1d4CD y4 y5 y6)))) * (((w1d4C y4 y5 y6 * w1d4C y4 y5 y6) * (w1d4C y4 y5 y6 * w1d4C y4 y5 y6)))⁻¹) := by
  unfold w1WCDD w1WDDOf
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1SEADD y4 y5 y6` shape. -/
theorem sh_SEADD (y4 y5 y6 : ℝ) :
    w1SEADD y4 y5 y6 = ((((matanDD (w1tA y4 y5 y6) * (w1tAD y4 y5 y6 * w1tAD y4 y5 y6)) * (w1aA y4 y5 y6)⁻¹) + (matanD (w1tA y4 y5 y6) * (((w1tADD y4 y5 y6 * w1aA y4 y5 y6) - (((2:ℝ) * w1tAD y4 y5 y6) * w1aAD y4 y5 y6)) * ((w1aA y4 y5 y6 * w1aA y4 y5 y6))⁻¹))) + (matan (w1tA y4 y5 y6) * ((((2:ℝ) * (w1aAD y4 y5 y6 * w1aAD y4 y5 y6)) - (w1aA y4 y5 y6 * w1aADD y4 y5 y6)) * ((w1aA y4 y5 y6 * (w1aA y4 y5 y6 * w1aA y4 y5 y6)))⁻¹))) := by
  unfold w1SEADD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1SEBDD y4 y5 y6` shape. -/
theorem sh_SEBDD (y4 y5 y6 : ℝ) :
    w1SEBDD y4 y5 y6 = ((((matanDD (w1tB y4 y5 y6) * (w1tBD y4 y5 y6 * w1tBD y4 y5 y6)) * (w1aB y4 y5 y6)⁻¹) + (matanD (w1tB y4 y5 y6) * (((w1tBDD y4 y5 y6 * w1aB y4 y5 y6) - (((2:ℝ) * w1tBD y4 y5 y6) * w1aBD y4 y5 y6)) * ((w1aB y4 y5 y6 * w1aB y4 y5 y6))⁻¹))) + (matan (w1tB y4 y5 y6) * ((((2:ℝ) * (w1aBD y4 y5 y6 * w1aBD y4 y5 y6)) - (w1aB y4 y5 y6 * w1aBDD y4 y5 y6)) * ((w1aB y4 y5 y6 * (w1aB y4 y5 y6 * w1aB y4 y5 y6)))⁻¹))) := by
  unfold w1SEBDD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1SECDD y4 y5 y6` shape. -/
theorem sh_SECDD (y4 y5 y6 : ℝ) :
    w1SECDD y4 y5 y6 = ((((matanDD (w1tC y4 y5 y6) * (w1tCD y4 y5 y6 * w1tCD y4 y5 y6)) * (w1aC y4 y5 y6)⁻¹) + (matanD (w1tC y4 y5 y6) * (((w1tCDD y4 y5 y6 * w1aC y4 y5 y6) - (((2:ℝ) * w1tCD y4 y5 y6) * w1aCD y4 y5 y6)) * ((w1aC y4 y5 y6 * w1aC y4 y5 y6))⁻¹))) + (matan (w1tC y4 y5 y6) * ((((2:ℝ) * (w1aCD y4 y5 y6 * w1aCD y4 y5 y6)) - (w1aC y4 y5 y6 * w1aCDD y4 y5 y6)) * ((w1aC y4 y5 y6 * (w1aC y4 y5 y6 * w1aC y4 y5 y6)))⁻¹))) := by
  unfold w1SECDD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1DIHAD y4 y5 y6` shape. -/
theorem sh_DIHAD (y4 y5 y6 : ℝ) :
    w1DIHAD y4 y5 y6 = ((w1WAD y4 y5 y6 * matan (w1gA y4 y5 y6)) + (w1WA y4 y5 y6 * (matanD (w1gA y4 y5 y6) * w1gAD y4 y5 y6))) := by
  unfold w1DIHAD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1DIHADD y4 y5 y6` shape. -/
theorem sh_DIHADD (y4 y5 y6 : ℝ) :
    w1DIHADD y4 y5 y6 = (((w1WADD y4 y5 y6 * matan (w1gA y4 y5 y6)) + ((((2:ℝ) * w1WAD y4 y5 y6) * w1gAD y4 y5 y6) * matanD (w1gA y4 y5 y6))) + ((w1WA y4 y5 y6 * (matanDD (w1gA y4 y5 y6) * (w1gAD y4 y5 y6 * w1gAD y4 y5 y6))) + (w1WA y4 y5 y6 * (matanD (w1gA y4 y5 y6) * w1gADD y4 y5 y6)))) := by
  unfold w1DIHADD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1DIHBD y4 y5 y6` shape. -/
theorem sh_DIHBD (y4 y5 y6 : ℝ) :
    w1DIHBD y4 y5 y6 = ((w1WBD y4 y5 y6 * matan (w1gB y4 y5 y6)) + (w1WB y4 y5 y6 * (matanD (w1gB y4 y5 y6) * w1gBD y4 y5 y6))) := by
  unfold w1DIHBD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1DIHBDD y4 y5 y6` shape. -/
theorem sh_DIHBDD (y4 y5 y6 : ℝ) :
    w1DIHBDD y4 y5 y6 = (((w1WBDD y4 y5 y6 * matan (w1gB y4 y5 y6)) + ((((2:ℝ) * w1WBD y4 y5 y6) * w1gBD y4 y5 y6) * matanD (w1gB y4 y5 y6))) + ((w1WB y4 y5 y6 * (matanDD (w1gB y4 y5 y6) * (w1gBD y4 y5 y6 * w1gBD y4 y5 y6))) + (w1WB y4 y5 y6 * (matanD (w1gB y4 y5 y6) * w1gBDD y4 y5 y6)))) := by
  unfold w1DIHBDD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1DIHCD y4 y5 y6` shape. -/
theorem sh_DIHCD (y4 y5 y6 : ℝ) :
    w1DIHCD y4 y5 y6 = ((w1WCD y4 y5 y6 * matan (w1gC y4 y5 y6)) + (w1WC y4 y5 y6 * (matanD (w1gC y4 y5 y6) * w1gCD y4 y5 y6))) := by
  unfold w1DIHCD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1DIHCDD y4 y5 y6` shape. -/
theorem sh_DIHCDD (y4 y5 y6 : ℝ) :
    w1DIHCDD y4 y5 y6 = (((w1WCDD y4 y5 y6 * matan (w1gC y4 y5 y6)) + ((((2:ℝ) * w1WCD y4 y5 y6) * w1gCD y4 y5 y6) * matanD (w1gC y4 y5 y6))) + ((w1WC y4 y5 y6 * (matanDD (w1gC y4 y5 y6) * (w1gCD y4 y5 y6 * w1gCD y4 y5 y6))) + (w1WC y4 y5 y6 * (matanD (w1gC y4 y5 y6) * w1gCDD y4 y5 y6)))) := by
  unfold w1DIHCDD
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `lfun (y4 * 0.5)` shape. -/
theorem sh_lf4 (y4 y5 y6 : ℝ) :
    lfun (y4 * 0.5) = ((h0 - (y4 * (0.5 : ℝ))) * ((h0 - 1))⁻¹) := by
  unfold lfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `lfun (y5 * 0.5)` shape. -/
theorem sh_lf5 (y4 y5 y6 : ℝ) :
    lfun (y5 * 0.5) = ((h0 - (y5 * (0.5 : ℝ))) * ((h0 - 1))⁻¹) := by
  unfold lfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `lfun (y6 * 0.5)` shape. -/
theorem sh_lf6 (y4 y5 y6 : ℝ) :
    lfun (y6 * 0.5) = ((h0 - (y6 * (0.5 : ℝ))) * ((h0 - 1))⁻¹) := by
  unfold lfun
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

/-- `w1F2 y4 y5 y6` shape. -/
theorem sh_D11 (y4 y5 y6 : ℝ) :
    w1F2 y4 y5 y6 = (((-(2 * mm1 / Real.pi) * (w1SEADD y4 y5 y6 + w1SEBDD y4 y5 y6 + w1SECDD y4 y5 y6)) + ((8 * mm2 / Real.pi) * (lfun (y4 * 0.5) * h0cut y4 * w1DIHCDD y4 y5 y6 + (2 * (-(25 / 13)) * w1DIHAD y4 y5 y6 + lfun (y5 * 0.5) * w1DIHADD y4 y5 y6) + lfun (y6 * 0.5) * w1DIHBDD y4 y5 y6))) - (0.008 * w1DIHCDD y4 y5 y6)) := by
  unfold w1F2
  try simp only [pow_two, pow_three, div_eq_mul_inv]
  try ring

end Kepler.Text.TaylorSecond
