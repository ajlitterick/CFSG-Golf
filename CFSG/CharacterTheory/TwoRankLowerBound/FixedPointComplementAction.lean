module

public import CFSG.CharacterTheory.TwoRankLowerBound.PermutationSubsetCoordinates

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem smul_mem_fixedPoints_iff {group points : Type*} [Group group] [MulAction group points]
    (element : group) (point : points) :
    element • point ∈ MulAction.fixedPoints group points ↔
      point ∈ MulAction.fixedPoints group points := by
  constructor
  · intro hfixed
    have hequal := MulAction.mem_fixedPoints.mp hfixed element⁻¹
    simp only [inv_smul_smul] at hequal
    exact hequal.symm ▸ hfixed
  · intro hfixed
    exact (MulAction.mem_fixedPoints.mp hfixed element).symm ▸ hfixed

instance fixedPointComplementMulAction {group points : Type*} [Group group] [MulAction group points] :
    MulAction group ((MulAction.fixedPoints group points)ᶜ : Set points) where
  smul := fun element point => ⟨element • point.val, by
    intro hfixed
    exact point.property ((smul_mem_fixedPoints_iff element point.val).mp hfixed)⟩
  one_smul := by intro point; apply Subtype.ext; exact one_smul group point.val
  mul_smul := by intros; apply Subtype.ext; exact mul_smul _ _ _


theorem permutationSubsetCoordinates_fixed_translation {ring group points : Type*}
    [CommRing ring] [Group group] [MulAction group points] [Fintype points]
    (element : group) :
    (LinearEquiv.conjAlgEquiv ring (permutationSubsetCoordinates (MulAction.fixedPoints group points)))
      (Representation.ofMulAction ring group points element) =
      LinearMap.prodMap LinearMap.id
        (Representation.ofMulAction ring group ((MulAction.fixedPoints group points)ᶜ : Set points) element) := by
  apply LinearMap.ext
  intro value
  apply Prod.ext
  · ext point
    change ((permutationSubsetCoordinates (MulAction.fixedPoints group points))
      ((Representation.ofMulAction ring group points element)
        ((permutationSubsetCoordinates (MulAction.fixedPoints group points)).symm value))).1.coeff point =
      value.1.coeff point
    rw [permutationSubsetCoordinates_fst_coeff, Representation.coeff_ofMulAction,
      MulAction.mem_fixedPoints.mp point.property element⁻¹,
      permutationSubsetCoordinates_symm_coeff_of_mem]
  · ext point
    change ((permutationSubsetCoordinates (MulAction.fixedPoints group points))
      ((Representation.ofMulAction ring group points element)
        ((permutationSubsetCoordinates (MulAction.fixedPoints group points)).symm value))).2.coeff point =
      ((Representation.ofMulAction ring group ((MulAction.fixedPoints group points)ᶜ : Set points)
        element) value.2).coeff point
    rw [permutationSubsetCoordinates_snd_coeff, Representation.coeff_ofMulAction,
      Representation.coeff_ofMulAction]
    exact permutationSubsetCoordinates_symm_coeff_of_not_mem _ value (element⁻¹ • point)

end CFSG.TwoRankLowerBound.Helpers
