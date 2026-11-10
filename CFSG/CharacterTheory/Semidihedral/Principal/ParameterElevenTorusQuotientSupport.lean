module

public import CFSG.CharacterTheory.Semidihedral.Principal.OrderOneTwentyFourInvolutionSum
public import CFSG.CharacterTheory.Semidihedral.Principal.RealOddPrincipalBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.SignedDegreeNumerics
public import CFSG.CharacterTheory.Semidihedral.Local.DerivedInvolutionsConjugate
public import CFSG.CharacterTheory.BlockBasics.LocalRing
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2FixedPointBound
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveOrdersSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
  CFSG.LyonsUnitaryFour CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.GorensteinWalter

namespace ParameterElevenTorus


theorem extendedCentralizer_le_normalizer_zpowers {G : Type*} [Group G] (x : G) :
    extendedCentralizer x ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  intro g hg
  have hy : Subgroup.zpowers (g⁻¹ * x * g) = Subgroup.zpowers x := by
    rcases (mem_extendedCentralizer x g).mp hg with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]
  have hconj : ∀ k : ℤ, (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
    intro k
    have h := conj_zpow (i := k) (a := g⁻¹) (b := x)
    rwa [inv_inv] at h
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hy]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hconj k⟩
  · intro hh
    rw [← hy] at hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [hconj k] at hk
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    simpa using hk


theorem case_one_false {g f δ : ℤ} (hf : 1 < f) (hδ : δ = 1 ∨ δ = -1)
    (hBr : g * (f + 11 * δ) ^ 2 = 15 * 2640 ^ 2 * (f * (f - δ)))
    (hOF : g * 20 ^ 2 * ((f + 11 * δ) ^ 2 * 11) = 2640 ^ 3 * (f * (f + δ) * 10)) : False := by
  have h1 : (2640 ^ 2 * f) * (26400 * (f + δ)) = (2640 ^ 2 * f) * (66000 * (f - δ)) := by
    linear_combination 4400 * hBr - hOF
  have h2 := mul_left_cancel₀ (by positivity : (2640 : ℤ) ^ 2 * f ≠ 0) h1
  rcases hδ with rfl | rfl <;> omega

theorem case_two_false {g f δ : ℤ} (hf : 1 < f) (hδ : δ = 1 ∨ δ = -1)
    (hBr : g * (f - 11 * δ) ^ 2 = 15 * 2640 ^ 2 * (f * (f + δ)))
    (hOF : g * 20 ^ 2 * ((f - 11 * δ) ^ 2 * 11) = 2640 ^ 3 * (f * (f + δ) * 12)) : False := by
  have hpos : 0 < f + δ := by rcases hδ with rfl | rfl <;> omega
  have h1 : (2640 ^ 2 * (f * (f + δ))) * 31680 = (2640 ^ 2 * (f * (f + δ))) * 66000 := by
    linear_combination 4400 * hBr - hOF
  have h2 := mul_left_cancel₀ (by positivity : (2640 : ℤ) ^ 2 * (f * (f + δ)) ≠ 0) h1
  omega


end ParameterElevenTorus

end CFSG.Semidihedral.Principal
