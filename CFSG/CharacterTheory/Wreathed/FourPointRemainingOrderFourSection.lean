module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseSections
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsSections
public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSupport

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FourPointRemainingOrderFour

open CFSG.TwoRankLowerBound.Helpers


theorem sum_mul_re_imCoeff_eq_zero {ι : Type*} (B : Finset ι) (W v : ι → ℂ) (i : ℂ)
    (h₁ : ∑ χ ∈ B, W χ * v χ = 0) (h₂ : ∑ χ ∈ B, W χ * conj (v χ) = 0) :
    ∑ χ ∈ B, W χ * ((v χ).re : ℂ) = 0 ∧
      ∑ χ ∈ B, W χ * ((FourPointGaussianColumns.imCoeff i (v χ) : ℝ) : ℂ) = 0 := by
  have hre : ∑ χ ∈ B, W χ * ((v χ).re : ℂ) =
      (∑ χ ∈ B, W χ * v χ + ∑ χ ∈ B, W χ * conj (v χ)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.re_eq_add_conj]
    ring
  have him : ∑ χ ∈ B, W χ * ((FourPointGaussianColumns.imCoeff i (v χ) : ℝ) : ℂ) =
      (∑ χ ∈ B, W χ * v χ - ∑ χ ∈ B, W χ * conj (v χ)) / (2 * Complex.I) / (i.im : ℂ) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [FourPointGaussianColumns.imCoeff, Complex.ofReal_div, Complex.im_eq_sub_conj]
    ring
  rw [hre, him, h₁, h₂]
  simp

end CFSG.Wreathed.FourPointRemainingOrderFour
