module

public import CFSG.CharacterTheory.TwoRankLowerBound.CoefficientBlocks
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerInduction

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem coefficientCharacterSpace_pairing_zero_outside {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index)
    (function : G → ℂ) (hfunction : function ∈ coefficientCharacterSpace basis support)
    (label : basis.index) (hnot : label ∉ support) :
    characterPairing function (basis.representation label).character = 0 := by
  induction hfunction using Submodule.span_induction with
  | mem generator hmember =>
    obtain ⟨member, hmember, rfl⟩ := hmember
    rw [characterPairing_irreducible _ _ (basis.irreducible member) (basis.irreducible label)]
    have hne : (basis.representation member).character ≠ (basis.representation label).character := by
      intro hequal
      exact hnot (basis.distinct hequal ▸ hmember)
    rw [ite_eq_right hne]
  | zero => simp [characterPairing]
  | add left right _ _ hleft hright =>
    simp only [characterPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add] at hleft hright ⊢
    rw [hleft, hright, add_zero]
  | smul scalar function _ hzero =>
    have hpair := congrFun ((characterBasisComplexCoordinates basis).map_smul scalar function) label
    change characterPairing (scalar • function) (basis.representation label).character =
      scalar * characterPairing function (basis.representation label).character at hpair
    rw [hpair, hzero, mul_zero]

theorem coefficientVirtualLattice_le_virtual {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    coefficientVirtualLattice basis support ≤ virtualCharacters G := by
  apply Submodule.span_le.mpr
  rintro _ ⟨label, _, rfl⟩
  exact character_mem_virtualCharacters _

theorem coefficientVirtualLattice_le_complex_space {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) :
    coefficientVirtualLattice basis support ≤ (coefficientCharacterSpace basis support).restrictScalars ℤ :=
  Submodule.span_le_restrictScalars ℤ ℂ _


end CFSG.TwoRankLowerBound.Helpers
