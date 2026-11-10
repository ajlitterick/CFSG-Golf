module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneQuotient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v


theorem thetaPlaneIntersection_map_equiv {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* H) (plane : Subgroup G) :
    (thetaPlaneIntersection prime plane).map equivalence.toMonoidHom =
      thetaPlaneIntersection prime (plane.map equivalence.toMonoidHom) := by
  have hcentral : equivalence.toMonoidHom.ker ≤ Subgroup.center G := by
    rw [MonoidHom.ker_eq_bot _ equivalence.injective]
    exact bot_le
  have hkernel : IsPGroup prime equivalence.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot _ equivalence.injective]
    exact IsPGroup.of_bot
  have hsymmCentral : equivalence.symm.toMonoidHom.ker ≤ Subgroup.center H := by
    rw [MonoidHom.ker_eq_bot _ equivalence.symm.injective]
    exact bot_le
  have hsymmKernel : IsPGroup prime equivalence.symm.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot _ equivalence.symm.injective]
    exact IsPGroup.of_bot
  apply le_antisymm
  · exact thetaPlaneIntersection_map_le_of_central_pKernel prime hprime equivalence.toMonoidHom
      equivalence.surjective hcentral hkernel plane
  · apply (Subgroup.map_le_map_iff_of_injective (f := equivalence.symm.toMonoidHom)
      equivalence.symm.injective).mp
    rw [subgroup_map_equiv_symm]
    have hle := thetaPlaneIntersection_map_le_of_central_pKernel prime hprime equivalence.symm.toMonoidHom
      equivalence.symm.surjective hsymmCentral hsymmKernel (plane.map equivalence.toMonoidHom)
    simpa only [subgroup_map_equiv_symm] using hle

theorem thetaPlaneCommutators_map_equiv {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* H) (plane : Subgroup G) :
    (thetaPlaneCommutators prime plane).map equivalence.toMonoidHom =
      thetaPlaneCommutators prime (plane.map equivalence.toMonoidHom) := by
  have hcentral : equivalence.toMonoidHom.ker ≤ Subgroup.center G := by
    rw [MonoidHom.ker_eq_bot _ equivalence.injective]
    exact bot_le
  have hkernel : IsPGroup prime equivalence.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot _ equivalence.injective]
    exact IsPGroup.of_bot
  have hsymmCentral : equivalence.symm.toMonoidHom.ker ≤ Subgroup.center H := by
    rw [MonoidHom.ker_eq_bot _ equivalence.symm.injective]
    exact bot_le
  have hsymmKernel : IsPGroup prime equivalence.symm.toMonoidHom.ker := by
    rw [MonoidHom.ker_eq_bot _ equivalence.symm.injective]
    exact IsPGroup.of_bot
  apply le_antisymm
  · exact thetaPlaneCommutators_map_le_of_central_pKernel prime hprime equivalence.toMonoidHom
      equivalence.surjective hcentral hkernel plane equivalence.injective.injOn
  · apply (Subgroup.map_le_map_iff_of_injective (f := equivalence.symm.toMonoidHom)
      equivalence.symm.injective).mp
    rw [subgroup_map_equiv_symm]
    have hle := thetaPlaneCommutators_map_le_of_central_pKernel prime hprime equivalence.symm.toMonoidHom
      equivalence.symm.surjective hsymmCentral hsymmKernel (plane.map equivalence.toMonoidHom)
      equivalence.symm.injective.injOn
    simpa only [subgroup_map_equiv_symm] using hle

theorem thetaPlaneAlpha_map_equiv {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (equivalence : G ≃* H) (plane : Subgroup G) :
    (thetaPlaneAlpha prime plane).map equivalence.toMonoidHom =
      thetaPlaneAlpha prime (plane.map equivalence.toMonoidHom) := by
  rw [thetaPlaneAlpha, Subgroup.map_sup, thetaPlaneCommutators_map_equiv prime hprime,
    thetaPlaneIntersection_map_equiv prime hprime]
  rfl


end CFSG.RankThreeEvenClassification.Helpers
