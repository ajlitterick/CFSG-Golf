module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterSubsetLattices
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterProjectionPairing
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalLocalSectionProjection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem coefficientCharacterSpace_mem_iff_class_and_pairing_zero_outside {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (support : Finset basis.index) (function : group → ℂ) :
    function ∈ coefficientCharacterSpace basis support ↔
      (∀ element conjugator, function (conjugator * element * conjugator⁻¹) = function element) ∧
      ∀ label, label ∉ support →
        characterPairing function (basis.representation label).character = 0 := by
  constructor
  · intro hfunction
    constructor
    · induction hfunction using Submodule.span_induction with
      | mem generator hmember =>
        obtain ⟨label, _, rfl⟩ := hmember
        intro element conjugator
        exact Representation.char_conj _ _ _
      | zero => intros; rfl
      | add left right _ _ hleft hright =>
        intro element conjugator
        simp only [Pi.add_apply, hleft, hright]
      | smul scalar function _ hequal =>
        intro element conjugator
        simp only [Pi.smul_apply, hequal]
    · exact coefficientCharacterSpace_pairing_zero_outside basis support function hfunction
  · rintro ⟨hclass, hzero⟩
    have hexpansion : function = ∑ label : basis.index,
        characterPairing function (basis.representation label).character •
          (basis.representation label).character := by
      funext element
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        finiteIrreducibleCharacterBasis_reconstruction basis function hclass element
    rw [hexpansion]
    apply Submodule.sum_mem
    intro label _
    by_cases hlabel : label ∈ support
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨label, hlabel, rfl⟩)
    · rw [hzero label hlabel, zero_smul]
      exact (coefficientCharacterSpace basis support).zero_mem

theorem supported_inducedFunction_mem_coefficientCharacterSpace {group : Type*}
    [Group group] [Fintype group] (subgroup : Subgroup group)
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (localBasis : FiniteIrreducibleCharacterBasis subgroup) (localSupport : Finset localBasis.index)
    (domain : Set subgroup) (function : subgroup → ℂ)
    (hspace : function ∈ coefficientCharacterSpace localBasis localSupport)
    (hsupport : ∀ element, element ∉ domain → function element = 0)
    (hzero : ∀ label, label ∉ support → ∀ element, element ∈ domain →
      characterSubsetProjection localBasis localSupport
        (fun member => (basis.representation label).character member.val) element⁻¹ = 0) :
    inducedFunction subgroup function ∈ coefficientCharacterSpace basis support := by
  apply (coefficientCharacterSpace_mem_iff_class_and_pairing_zero_outside basis support _).mpr
  refine ⟨inducedFunction_conjugate subgroup function, ?_⟩
  intro label hlabel
  rw [characterPairing_inducedFunction_left subgroup function _
    (fun element conjugator => Representation.char_conj _ _ _)]
  exact coefficientCharacterSpace_pairing_zero_of_projected_inverse_support
    localBasis localSupport domain function _ hspace hsupport (hzero label hlabel)


end CFSG.TwoRankLowerBound.Helpers
