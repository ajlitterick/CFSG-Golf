module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicFiveInversionFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.OrderOneTwentyFourInvolutionSum
public import CFSG.LocalAnalysis.LyonsUnitaryFour.SylowColumns.OrderFormula
public import CFSG.CharacterTheory.BlockBasics.LocalRing

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour

namespace ParameterNineNonregular

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


theorem padicValNat_eq_of_eq_pow_mul {N p k a : ℕ} (hp : p.Prime) (hN : N = p ^ k * a)
    (ha : ¬ p ∣ a) : padicValNat p N = k := by
  have : Fact p.Prime := ⟨hp⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (dvd_zero p)
  rw [hN, padicValNat.mul (pow_ne_zero _ hp.ne_zero) ha0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd ha, add_zero]


end ParameterNineNonregular

end CFSG.Semidihedral.Principal
