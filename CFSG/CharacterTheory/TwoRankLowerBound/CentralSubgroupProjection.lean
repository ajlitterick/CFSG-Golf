module

public import CFSG.CharacterTheory.TwoRankLowerBound.SubgroupCoefficientProjection
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterResidueCompleteness
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCoefficientReduction

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebra_central_of_coeff_conjugation {G : Type*} [Group G] [Fintype G]
    (value : MonoidAlgebra ℂ G)
    (hinvariant : ∀ element conjugator : G,
      value.coeff (conjugator * element * conjugator⁻¹) = value.coeff element) :
    ∀ other : MonoidAlgebra ℂ G, Commute value other := by
  rw [← groupAlgebraClassElement_of_coeff value]
  apply groupAlgebraClassElement_central
  intro element conjugator
  have hinverse : (conjugator * element * conjugator⁻¹)⁻¹ =
      conjugator * element⁻¹ * conjugator⁻¹ := by group
  rw [hinverse]
  exact hinvariant element⁻¹ conjugator

@[expose] noncomputable def centralSubgroupCoefficientProjection {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (subgroup : Subgroup G) :
    centralCoefficientSubring (G := G) ring →+ centralCoefficientSubring (G := subgroup) ring where
  toFun value := ⟨subgroupCoefficientProjection subgroup value.val, by
    constructor
    · intro element
      rw [subgroupCoefficientProjection_coeff]
      exact centralCoefficientSubring_coefficients ring value element.val
    · apply Subring.mem_center_iff.mpr
      intro other
      apply Commute.symm
      apply groupAlgebra_central_of_coeff_conjugation
      intro element conjugator
      simp only [subgroupCoefficientProjection_coeff, Subgroup.coe_mul, Subgroup.coe_inv]
      exact central_groupAlgebra_coeff_conjugation value.val
        (centralCoefficientSubring_commutes ring value) element.val conjugator.val⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' left right := Subtype.ext (map_add _ left.val right.val)

theorem centralSubgroupCoefficientProjection_val {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (subgroup : Subgroup G)
    (value : centralCoefficientSubring (G := G) ring) :
    (centralSubgroupCoefficientProjection ring subgroup value).val =
      subgroupCoefficientProjection subgroup value.val := rfl


theorem centralSubgroupCoefficientProjection_scalar {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (subgroup : Subgroup G) (scalar : ring) :
    centralSubgroupCoefficientProjection ring subgroup (centralCoefficientScalarHom ring scalar) =
      centralCoefficientScalarHom ring scalar := by
  apply Subtype.ext
  change subgroupCoefficientProjection subgroup (MonoidAlgebra.single 1 scalar.val) =
    MonoidAlgebra.single 1 scalar.val
  ext element
  rw [subgroupCoefficientProjection_coeff]
  have hequal : (1 : G) = element.val ↔ (1 : subgroup) = element :=
    ⟨fun hequal => Subtype.ext hequal, fun hequal => congrArg Subtype.val hequal⟩
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, hequal]

theorem centralCoefficientLiftHom_coeff {G : Type*} [Group G] [Fintype G]
    (ring : Subring ℂ) (value : centralCoefficientSubring (G := G) ring) (element : G) :
    (centralCoefficientLiftHom ring value).coeff element =
      ⟨value.val.coeff element, centralCoefficientSubring_coefficients ring value element⟩ := by
  apply Subtype.ext
  have hequal := congrArg (fun algebraElement : MonoidAlgebra ℂ G => algebraElement.coeff element)
    (centralCoefficientLiftHom_map ring value)
  exact (MonoidAlgebra.coeff_mapRingHom ring.subtype _ element).symm.trans hequal


theorem centralCoefficientReductionHom_conjugationInvariant {G : Type*}
    [Group G] [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (value : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal))
    (subgroup : Subgroup G) :
    subgroupConjugationInvariant subgroup (centralCoefficientReductionHom ideal value) := by
  intro conjugator element
  simp only [centralCoefficientReductionHom, RingHom.comp_apply, MonoidAlgebra.coeff_mapRingHom,
    centralCoefficientLiftHom_coeff]
  congr 1
  apply Subtype.ext
  exact central_groupAlgebra_coeff_conjugation value.val
    (centralCoefficientSubring_commutes _ value) element conjugator.val


end CFSG.TwoRankLowerBound.Helpers
