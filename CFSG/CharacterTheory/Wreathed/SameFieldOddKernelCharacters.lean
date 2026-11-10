module

public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelFixedSpace
public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelSections
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.SquareRootSmallCharacterRigidity
open scoped BigOperators Classical

variable {G : Type} [Group G]

theorem original_irreducible_affording_exists (β : CFSG.BlocksIrr G) :
    ∃ ρ : FiniteComplexRepresentation.{0, 0} G,
      ρ.IsIrreducible ∧ ρ.character = (β : G → ℂ) := by
  simpa only [CFSG.blocksIrr_eq_irreducible_characters, Set.mem_ofPred_eq] using β.property

@[expose] def affordingComplexRepresentation (β : CFSG.BlocksIrr G) :
    FiniteComplexRepresentation.{0, 0} G :=
  Classical.choose (original_irreducible_affording_exists β)

theorem affordingComplexRepresentation_spec (β : CFSG.BlocksIrr G) :
    (affordingComplexRepresentation β).IsIrreducible ∧
      (affordingComplexRepresentation β).character = (β : G → ℂ) :=
  Classical.choose_spec (original_irreducible_affording_exists β)


@[expose] def oddKernelQuotientCharacterRepresentation (β : CFSG.BlocksIrr G)
    (K : Subgroup G) (O : Subgroup K) [O.Normal] :
    FiniteComplexRepresentation.{0, 0} (K ⧸ O) where
  vector := Representation.invariants
    (((affordingComplexRepresentation β).representation.comp K.subtype).comp O.subtype)
  representation := fixedSpaceQuotientRepresentation
    (affordingComplexRepresentation β).representation K O


theorem oddKernelQuotientCharacterRepresentation_degree_le
    (β : CFSG.BlocksIrr G) (K : Subgroup G) (O : Subgroup K) [O.Normal]
    (Q : ℕ) (hβdegree : (β : G → ℂ) 1 = (Q : ℂ)) :
    Module.finrank ℂ (oddKernelQuotientCharacterRepresentation β K O).vector ≤ Q := by
  have hfinrank : Module.finrank ℂ (affordingComplexRepresentation β).vector = Q := by
    have hdegree := congrFun (affordingComplexRepresentation_spec β).2 1
    rw [hβdegree] at hdegree
    change (affordingComplexRepresentation β).representation.character 1 = (Q : ℂ) at hdegree
    rw [Representation.char_one] at hdegree
    exact_mod_cast hdegree
  exact hfinrank ▸ Submodule.finrank_le _

theorem oddKernelQuotientCharacterRepresentation_degree_eq_iff
    {β : CFSG.BlocksIrr G} {K : Subgroup G} {O : Subgroup K} [O.Normal]
    (Q : ℕ) (hβdegree : (β : G → ℂ) 1 = (Q : ℂ)) :
    Module.finrank ℂ (oddKernelQuotientCharacterRepresentation β K O).vector = Q ↔
      O.map K.subtype ≤ MonoidHom.ker (affordingComplexRepresentation β).representation := by
  have hfinrank : Module.finrank ℂ (affordingComplexRepresentation β).vector = Q := by
    have hdegree := congrFun (affordingComplexRepresentation_spec β).2 1
    rw [hβdegree] at hdegree
    change (affordingComplexRepresentation β).representation.character 1 = (Q : ℂ) at hdegree
    rw [Representation.char_one] at hdegree
    exact_mod_cast hdegree
  rw [← hfinrank]
  change Module.finrank ℂ (Representation.invariants
    (((affordingComplexRepresentation β).representation.comp K.subtype).comp O.subtype)) =
      Module.finrank ℂ (affordingComplexRepresentation β).vector ↔ _
  rw [finrank_invariants_eq_finrank_iff, Subgroup.map_le_iff_le_comap, MonoidHom.comap_ker]


theorem oddKernel_eq_bot_of_original_layer_character_degree [IsSimpleGroup G]
    (β : CFSG.BlocksIrr G) (Q : ℕ) (hQ : 1 < Q)
    (hβdegree : (β : G → ℂ) 1 = (Q : ℂ))
    (K : Subgroup G) (O : Subgroup K) [O.Normal] (L : Subgroup (K ⧸ O))
    (hθLdegree : Module.finrank ℂ
      (fixedSpaceLayerComplexRepresentation (affordingComplexRepresentation β).representation
        K O L).vector = Q) : O = ⊥ := by
  let ρ := affordingComplexRepresentation β
  let : ρ.representation.IsIrreducible := (affordingComplexRepresentation_spec β).1
  have hρdegree : ρ.character 1 = (Q : ℂ) := by
    rw [(affordingComplexRepresentation_spec β).2, hβdegree]
  have hρkernel : MonoidHom.ker ρ.representation = ⊥ :=
    irreducible_ker_eq_bot_of_degree_ne_one ρ.representation (by
      change ρ.character 1 ≠ 1
      rw [hρdegree]
      intro heq
      have hQone : Q = 1 := by exact_mod_cast heq
      omega)
  have hOimage := (oddKernelQuotientCharacterRepresentation_degree_eq_iff
    (β := β) (K := K) (O := O) Q hβdegree).mp hθLdegree
  exact subgroup_eq_bot_of_image_le_ker ρ.representation hρkernel K O hOimage

end CFSG.Wreathed.SameFieldOddKernel
