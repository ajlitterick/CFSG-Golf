module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitNormal
public import Mathlib.GroupTheory.Solvable

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

open scoped commutatorElement

variable {K : Type*} [Field K]

abbrev SpecialQuotient (K : Type*) [Field K] :=
  DeterminantIsometries K ⧸ specialImage K

@[expose] def quotientLeftRightImage (K : Type*) [Field K] : Subgroup (SpecialQuotient K) :=
  (leftRightImage K).map (QuotientGroup.mk' (specialImage K))

instance quotientLeftRightImageNormal : (quotientLeftRightImage K).Normal :=
  (leftRightImageNormal (K := K)).map _ (QuotientGroup.mk'_surjective _)

theorem commonDeterminant_commutator (z w : equalDeterminants K) :
    commonDeterminant ⁅z, w⁆ = 1 := by
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem leftRightImage_commutator_mem_specialImage {g h : DeterminantIsometries K}
    (hg : g ∈ leftRightImage K) (hh : h ∈ leftRightImage K) :
    ⁅g, h⁆ ∈ specialImage K := by
  obtain ⟨z, rfl⟩ := hg
  obtain ⟨w, rfl⟩ := hh
  rw [← map_commutatorElement]
  exact rho_mem_specialImage_of_commonDeterminant _ (commonDeterminant_commutator z w)

theorem quotientLeftRightImage_mul_comm {g h : SpecialQuotient K}
    (hg : g ∈ quotientLeftRightImage K) (hh : h ∈ quotientLeftRightImage K) :
    g * h = h * g := by
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨b, hb, rfl⟩ := hh
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (leftRightImage_commutator_mem_specialImage ha hb)

instance quotientLeftRightImageCommutative : IsMulCommutative (quotientLeftRightImage K) :=
  IsMulCommutative.of_setLike_mul_comm (fun _ ha _ hb => quotientLeftRightImage_mul_comm ha hb)

theorem quotientLeftRightImage_index :
    (quotientLeftRightImage K).index = (leftRightImage K).index := by
  apply Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  exact specialImage_le_leftRightImage

theorem quotientLeftRightImage_index_dvd_two : (quotientLeftRightImage K).index ∣ 2 := by
  rw [quotientLeftRightImage_index]
  exact leftRightImage_index_dvd_two


instance quotientByLeftRightImageCyclic :
    IsCyclic (SpecialQuotient K ⧸ quotientLeftRightImage K) := by
  apply isCyclic_of_card_dvd_prime (p := 2)
  exact quotientLeftRightImage_index_dvd_two

instance specialQuotientSolvable : Group.IsSolvable (SpecialQuotient K) :=
  Group.isSolvable_of_subgroup_quotient (quotientLeftRightImage K)


end CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
