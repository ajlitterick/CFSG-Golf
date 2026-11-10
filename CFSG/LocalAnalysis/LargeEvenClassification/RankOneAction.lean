module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse


theorem binary_GL_two_card_dvd {dimension : ℕ} (hdimension : dimension ≤ 2) :
    Nat.card (GL (Fin dimension) (ZMod 2)) ∣ 6 := by
  rw [Matrix.card_GL_field]
  interval_cases dimension <;> norm_num [Fin.prod_univ_succ]

theorem two_group_two_generator_aut_prime_support {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : pGeneratorRank 2 Ambient ≤ 2)
    {prime : ℕ} (hprime : prime.Prime) (hdivides : prime ∣ Nat.card (MulAut Ambient)) :
    prime = 2 ∨ prime = 3 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup Nat.prime_two hpgroup
  let module : Module (ZMod 2) (Additive (Ambient ⧸ frattini Ambient)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two hpgroup)
  let linearAction := (elementaryAutLinear 2).comp (frattiniAutAction Ambient)
  have hlinearKernel : linearAction.ker = (frattiniAutAction Ambient).ker := by
    ext automorphism
    change elementaryAutLinear 2 (frattiniAutAction Ambient automorphism) = 1 ↔
      frattiniAutAction Ambient automorphism = 1
    constructor
    · intro heq
      apply elementaryAutLinear_injective 2
      exact heq.trans (map_one (elementaryAutLinear 2)).symm
    · intro heq
      rw [heq, map_one]
  have hkernelGroup : IsPGroup 2 linearAction.ker := by
    rw [hlinearKernel]
    exact frattiniAutAction_isPGroup_ker Ambient Nat.prime_two hpgroup
  obtain ⟨kernelRank, hkernelCard⟩ := hkernelGroup.exists_card_eq
  have hdimension : Module.finrank (ZMod 2) (Additive (Ambient ⧸ frattini Ambient)) ≤ 2 := by
    rw [← pGeneratorRank_eq_frattini_finrank Nat.prime_two hpgroup module]
    exact hrank
  have hrangeDivides : Nat.card linearAction.range ∣ 6 := by
    have hcard := linearAction.range.card_subgroup_dvd_card
    rw [card_linear_aut_binary] at hcard
    exact hcard.trans (binary_GL_two_card_dvd hdimension)
  have hformula := Subgroup.card_eq_card_quotient_mul_card_subgroup linearAction.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange linearAction).toEquiv, hkernelCard] at hformula
  rw [hformula] at hdivides
  rcases hprime.dvd_mul.mp hdivides with himage | hkernel
  · have hsmallDivides : prime ∣ 6 := himage.trans hrangeDivides
    have hfactorization : 6 = 2 * 3 := by norm_num
    rw [hfactorization] at hsmallDivides
    rcases hprime.dvd_mul.mp hsmallDivides with htwo | hthree
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp htwo)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hprime (by norm_num)).mp hthree)
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hkernel))

theorem rank_one_two_group_aut_prime_support_exact {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    {prime : ℕ} (hprime : prime.Prime) (hdivides : prime ∣ Nat.card (MulAut Ambient)) :
    prime = 2 ∨ prime = 3 :=
  two_group_two_generator_aut_prime_support hpgroup
    (rank_one_two_group_generator_rank_le_two hpgroup hrank) hprime hdivides


end CFSG.LargeEvenClassification.Helpers
