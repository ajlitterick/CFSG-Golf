module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityIntrinsic

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G]

theorem actual_root_odd_power_column_section_value
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n))
    (h : ℤ) (hh : Odd h) (v : G) (hv : Odd (orderOf v))
    (hc : v ∈ Subgroup.centralizer ({actualRoot S e} : Set G)) :
    oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n)
      (actualRoot S e ^ h * v) = 4 := by
  let I := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  let c : basis.index → ℕ → ℤ := fun χ r =>
    signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e) root (2 ^ n) r
  have hhalf : 0 < 2 ^ n / 2 := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨hvalues, hgram, _, _, _, _⟩ :=
    CFSG.Wreathed.ConditionalSquareRoot.actualRoot_signed_even_columns n hn S e basis ideal
      principal hprincipal hroot
  have hc0 : ∀ χ, c χ 0 =
      oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) := by
    intro χ
    simp only [c, signedEvenEigenmultiplicity, oddPowerCoefficient, mul_zero, zero_add]
  change (∑ χ ∈ I,
    (oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) : ℂ) *
      (basis.representation χ).character (actualRoot S e ^ h * v)) = 4
  simp only [← hc0]
  calc
    (∑ χ ∈ I, (c χ 0 : ℂ) * (basis.representation χ).character
        (actualRoot S e ^ h * v)) =
        ∑ χ ∈ I, ∑ r ∈ Finset.range (2 ^ n / 2),
          (c χ 0 : ℂ) * (c χ r : ℂ) * (root ^ 2) ^ ((r : ℤ) * h) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [(hvalues χ hχ h hh v hc hv).1, (hvalues χ hχ h hh v hc hv).2,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = ∑ r ∈ Finset.range (2 ^ n / 2),
        ((∑ χ ∈ I, c χ 0 * c χ r : ℤ) : ℂ) * (root ^ 2) ^ ((r : ℤ) * h) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      push_cast
      rw [Finset.sum_mul]
    _ = 4 := by
      rw [Finset.sum_eq_single 0]
      · rw [hgram 0 hhalf 0 hhalf, ite_eq_left rfl]
        simp
      · intro r hr hr0
        rw [hgram 0 hhalf r (Finset.mem_range.mp hr), ite_eq_right (Ne.symm hr0)]
        simp
      · intro h0
        exact (h0 (Finset.mem_range.mpr hhalf)).elim

theorem actual_root_principal_average_indicator
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    ∀ g : G, rootPrincipalAverageColumn n ideal (actualRoot S e) g =
      if g ∈ squareRootSection (actualRoot S e) then 4 else 0 := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  let root := Complex.exp (2 * Real.pi * Complex.I / (2 * 2 ^ n : ℕ))
  have hroot : IsPrimitiveRoot root (2 * 2 ^ n) :=
    Complex.isPrimitiveRoot_exp _ (by positivity)
  rw [actual_root_principal_average_column_eq n hn S e basis ideal principal hprincipal
    root hroot]
  have hclass : BlocksIsClassFunction
      (oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n)) := by
    intro g a
    unfold oddPowerPrincipalColumn
    exact Finset.sum_congr rfl fun χ _ => congrArg
      (fun z : ℂ =>
        (oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) : ℂ) * z)
      (Representation.char_conj (basis.representation χ).representation g a)
  have hon := (classFunction_section_value_iff hclass).mp
    (fun h v hh hv hc => actual_root_odd_power_column_section_value n hn S e basis ideal
      principal hprincipal root hroot h hh v hv hc)
  intro g
  split_ifs with hg
  · exact hon g hg
  · exact actual_root_odd_power_column_support n hn S e basis ideal principal hprincipal
      root hroot g hg


end CFSG.Wreathed.SquareRootSmallCharacterRigidity
