module

public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerBimoduleReduction
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalAverageQuotient

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem p_centralizer_projection_augmentation {field group : Type*}
    [Field field] [Group group] [Fintype group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (subgroup : Subgroup group) (hgroup : IsPGroup prime subgroup) (value : MonoidAlgebra field group)
    (hinvariant : subgroupConjugationInvariant subgroup value) :
    groupAlgebraAugmentation field (Subgroup.centralizer (subgroup : Set group))
      (subgroupCoefficientProjection (Subgroup.centralizer (subgroup : Set group)) value) =
      groupAlgebraAugmentation field group value := by
  let : MulAction subgroup group := subgroupConjugationAction subgroup
  rw [groupAlgebraAugmentation_sum, groupAlgebraAugmentation_sum]
  simp only [subgroupCoefficientProjection_coeff]
  have hequal := p_group_invariant_sum_fixedPoints prime hgroup (fun element => value.coeff element)
    (fun element member => hinvariant element member)
  simp only [conjugation_fixedPoints_iff_centralizer] at hequal
  rw [hequal, ← Finset.sum_filter]
  symm
  apply Finset.sum_subtype
  intro member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]


end CFSG.TwoRankLowerBound.Helpers
