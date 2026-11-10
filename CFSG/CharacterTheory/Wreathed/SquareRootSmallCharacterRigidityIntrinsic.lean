module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityThreeLabels
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityMinimalDegree

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

@[expose] def rootCharacterAverage {G : Type} [Group G] (n : ℕ) (y : G) (χ : G → ℂ) : ℂ :=
  ((2 ^ n : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ n), χ (y ^ (2 * k + 1))

@[expose] def rootPrincipalAverageColumn {G : Type} [Group G] (n : ℕ)
    (ideal : Ideal ComplexAlgebraicIntegers) (y : G) : G → ℂ :=
  fun g => ∑ᶠ χ ∈ BlocksPrincipalBlock ideal G, rootCharacterAverage n y χ * χ g


theorem actual_root_principal_average_column_eq {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    rootPrincipalAverageColumn n ideal (actualRoot S e) =
      oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) := by
  ext g
  unfold rootPrincipalAverageColumn
  change (∑ᶠ χ ∈ BlocksBlockOf ideal G (1 : G → ℂ),
    rootCharacterAverage n (actualRoot S e) χ * χ g) = _
  rw [← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal,
    finsum_mem_image basis.distinct.injOn, finsum_mem_coe_finset]
  apply Finset.sum_congr rfl
  intro χ _
  rw [show rootCharacterAverage n (actualRoot S e) (basis.representation χ).character =
    (oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) : ℂ) from
      actual_root_odd_power_average n hn S e (basis.representation χ) root hroot]

variable {G : Type} [Group G] [Fintype G]

private theorem intrinsic_basis_principal :
    ∃ (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
      (basis.representation principal).character = 1 := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  exact ⟨basis, principal, hprincipal⟩

theorem actual_root_intrinsic_integral_column
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    rootPrincipalAverageColumn n ideal (actualRoot S e) ∈ BlocksVChar G ∧
      (∀ g ∉ squareRootSection (actualRoot S e),
        rootPrincipalAverageColumn n ideal (actualRoot S e) g = 0) ∧
      rootPrincipalAverageColumn n ideal (actualRoot S e) 1 = 0 ∧
      BlocksInnerProduct (1 : G → ℂ) (rootPrincipalAverageColumn n ideal (actualRoot S e)) = 1 ∧
      ∀ θ : FiniteComplexRepresentation.{0, 0} G,
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        BlocksInnerProduct θ.character (rootPrincipalAverageColumn n ideal (actualRoot S e)) =
          -1 := by
  obtain ⟨basis, principal, hprincipal⟩ := intrinsic_basis_principal (G := G)
  let root := Complex.exp (2 * Real.pi * Complex.I / (2 * 2 ^ n : ℕ))
  have hroot : IsPrimitiveRoot root (2 * 2 ^ n) :=
    Complex.isPrimitiveRoot_exp _ (by positivity)
  rw [actual_root_principal_average_column_eq n hn S e basis ideal principal hprincipal
    root hroot]
  obtain ⟨hvirtual, hoff, hzero, _, _⟩ := actual_root_integral_odd_power_column
    n hn S e basis ideal principal hprincipal root hroot
  refine ⟨hvirtual, hoff, hzero, ?_, ?_⟩
  · rw [oddPowerPrincipalColumn_principal_pairing basis ideal principal hprincipal,
      actual_root_odd_power_principal_coefficient n hn S e basis principal hprincipal root hroot]
    norm_num
  · exact fun θ hθ => actual_section_minus_one_column_pairing n hn S e basis ideal principal
      hprincipal root hroot θ hθ


end CFSG.Wreathed.SquareRootSmallCharacterRigidity
