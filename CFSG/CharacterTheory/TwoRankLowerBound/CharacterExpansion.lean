module

public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualCharacters

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

universe groupUniverse vectorUniverse

theorem characterPairing_distinct_expansion_coefficient
    {G : Type groupUniverse} [Group G] [Fintype G] {index : Type*} [Fintype index]
    (representation : index → FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G)
    (hirreducible : ∀ label, (representation label).IsIrreducible)
    (hdistinct : Function.Injective (fun label => (representation label).character))
    (coefficient : index → ℂ) (target : index) :
    characterPairing
      (fun element => ∑ label, coefficient label * (representation label).character element)
      (representation target).character = coefficient target := by
  rw [characterPairing_expansion_left]
  simp_rw [characterPairing_irreducible _ _ (hirreducible _) (hirreducible target)]
  simp [hdistinct.eq_iff]

theorem characterPairing_distinct_expansion_norm
    {G : Type groupUniverse} [Group G] [Fintype G] {index : Type*} [Fintype index]
    (representation : index → FiniteComplexRepresentation.{groupUniverse, vectorUniverse} G)
    (hirreducible : ∀ label, (representation label).IsIrreducible)
    (hdistinct : Function.Injective (fun label => (representation label).character))
    (coefficient : index → ℂ) :
    characterPairing
      (fun element => ∑ label, coefficient label * (representation label).character element)
      (fun element => ∑ label, coefficient label * (representation label).character element) =
      ∑ label, coefficient label ^ 2 := by
  rw [characterPairing_expansion_right]
  simp_rw [characterPairing_distinct_expansion_coefficient representation hirreducible hdistinct]
  simp only [pow_two]


structure IrreducibleCharacterExpansion (G : Type groupUniverse) [Group G]
    (function : G → ℂ) where
  index : Type groupUniverse
  [fintype : Fintype index]
  representation : index → FiniteComplexRepresentation.{groupUniverse, groupUniverse} G
  irreducible : ∀ label, (representation label).IsIrreducible
  distinct : Function.Injective (fun label => (representation label).character)
  coefficient : index → ℤ
  expansion : ∀ element : G,
    function element = ∑ label, (coefficient label : ℂ) * (representation label).character element

attribute [instance] IrreducibleCharacterExpansion.fintype

set_option backward.isDefEq.respectTransparency false in
theorem virtualCharacter_exists_irreducibleCharacterExpansion
    {G : Type groupUniverse} [Group G] [Finite G] {function : G → ℂ}
    (hvirtual : function ∈ virtualCharacters G) :
    Nonempty (IrreducibleCharacterExpansion G function) := by
  obtain ⟨support, coefficient, hsupport, hsum⟩ :=
    virtualCharacter_exists_distinct_irreducible_expansion hvirtual
  choose representation hirreducible hequal using (fun label : support =>
    hsupport label label.property)
  refine ⟨{
    index := support
    representation := representation
    irreducible := hirreducible
    distinct := ?_
    coefficient := fun label => coefficient label
    expansion := ?_ }⟩
  · intro left right heq
    apply Subtype.ext
    rw [← hequal left, ← hequal right]
    exact heq
  · intro element
    rw [hsum, Finset.sum_subtype support (by intros; rfl)]
    apply Finset.sum_congr rfl
    intro label _
    rw [hequal label]


end CFSG.TwoRankLowerBound.Helpers
