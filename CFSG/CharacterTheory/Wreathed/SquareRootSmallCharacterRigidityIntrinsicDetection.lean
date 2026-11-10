module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigiditySignedCore

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ActualProjectiveLayer
open CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.ConditionalGeneralBase
open CFSG.BlockSectionOrthogonality.Helpers CFSG.Semidihedral.Principal
open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G]


theorem irreducible_actual_finite_representation (χ : BlocksIrr G) :
    ∃ θ : FiniteComplexRepresentation.{0, 0} G,
      θ.character = (χ : G → ℂ) ∧ Module.finrank ℂ θ.vector = irreducibleDegree χ := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨label, hlabel⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis χ.property
  refine ⟨basis.representation label, hlabel, ?_⟩
  have h := congrFun hlabel 1
  change (basis.representation label).representation.character 1 = (χ : G → ℂ) 1 at h
  rw [Representation.char_one, irreducibleDegree_cast] at h
  exact_mod_cast h

@[expose] def originalSectionPassingIrreducibles (y : G) : Set (BlocksIrr G) :=
  {χ | ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
    v ∈ Subgroup.centralizer ({y} : Set G) → (χ : G → ℂ) (y ^ h * v) = -1}

@[expose] def originalSectionLeastDegree (y : G) : ℕ :=
  sInf (irreducibleDegree '' originalSectionPassingIrreducibles y)


end CFSG.Wreathed.SquareRootSmallCharacterRigidity
