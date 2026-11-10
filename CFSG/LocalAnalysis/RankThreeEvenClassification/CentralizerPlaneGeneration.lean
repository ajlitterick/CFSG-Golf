module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ActionPlaneGeneration

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose, instance_reducible]
def normalizedConjugationAction {G : Type u} [Group G]
    (actor subgroup : Subgroup G)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    MulDistribMulAction actor subgroup where
  smul member element := ⟨member * element * (member : G)⁻¹,
    Subgroup.le_normalizer_iff.mp hnormalizes member member.property element element.property⟩
  one_smul element := Subtype.ext (by
    change (1 : G) * (element : G) * (1 : G)⁻¹ = element
    simp)
  mul_smul first second element := Subtype.ext (by
    change ((first : G) * second) * (element : G) * ((first : G) * second)⁻¹ =
      first * ((second : G) * element * (second : G)⁻¹) * (first : G)⁻¹
    simp [mul_assoc])
  smul_one member := Subtype.ext (by
    change (member : G) * 1 * (member : G)⁻¹ = 1
    simp)
  smul_mul member first second := Subtype.ext (by
    change (member : G) * ((first : G) * second) * (member : G)⁻¹ =
      (member * first * (member : G)⁻¹) * (member * second * (member : G)⁻¹)
    simp [mul_assoc])


end CFSG.RankThreeEvenClassification.Helpers
