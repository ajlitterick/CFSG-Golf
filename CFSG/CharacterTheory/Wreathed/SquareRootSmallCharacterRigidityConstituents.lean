module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityIntegralAverage
public import CFSG.CharacterTheory.BlockBasics.Bridge

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

variable {G : Type} [Group G] [Fintype G]

theorem innerProduct_finite_integral_column {ι : Type*} (I : Finset ι)
    (f : G → ℂ) (χ : ι → G → ℂ) (c : ι → ℤ) :
    BlocksInnerProduct f (∑ i ∈ I, c i • χ i) =
      ∑ i ∈ I, (c i : ℂ) * BlocksInnerProduct f (χ i) := by
  induction I using Finset.induction_on with
  | empty => simp [BlocksInnerProduct]
  | @insert i I hi hI =>
    rw [Finset.sum_insert hi, innerProduct_add_right, innerProduct_zsmul_right, hI,
      Finset.sum_insert hi]


theorem innerProduct_of_constant_on_support (U : Set G) (f T : G → ℂ) (δ : ℂ)
    (hT : ∀ g ∉ U, T g = 0) (hf : ∀ g ∈ U, f g = δ) :
    BlocksInnerProduct f T = δ * BlocksInnerProduct (1 : G → ℂ) T := by
  rw [innerProduct_eq_of_agree_on_support U f (fun _ => δ) T hT hf]
  unfold BlocksInnerProduct
  simp only [Pi.one_apply, one_mul]
  rw [← Finset.mul_sum]
  ring

theorem oddPowerPrincipalColumn_principal_pairing
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsPrime] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (y : G) (root : ℂ) (m : ℕ) :
    BlocksInnerProduct (1 : G → ℂ) (oddPowerPrincipalColumn basis ideal principal y root m) =
      (oddPowerCoefficient (basis.representation principal) y root m : ℂ) := by
  have hcolumn : oddPowerPrincipalColumn basis ideal principal y root m =
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddPowerCoefficient (basis.representation χ) y root m •
          (basis.representation χ).character := by
    ext g
    simp only [oddPowerPrincipalColumn, Finset.sum_apply, zsmul_eq_mul,
      Pi.mul_apply, Pi.intCast_apply]
  rw [hcolumn, innerProduct_finite_integral_column]
  have hpair (χ : basis.index) :
      BlocksInnerProduct (1 : G → ℂ) (basis.representation χ).character =
        if χ = principal then 1 else 0 := by
    rw [← hprincipal, blocksInnerProduct_eq_characterPairing _
      (AddSubgroup.subset_closure (CFSG.BlockBasics.basis_character_mem_irr basis χ))]
    simpa only [basis.distinct.eq_iff, eq_comm] using
      characterPairing_irreducible (basis.representation principal) (basis.representation χ)
        (basis.irreducible principal) (basis.irreducible χ)
  simp only [hpair, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', coefficientBlock_self_mem, ite_true]

theorem actual_section_minus_one_column_pairing
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n))
    (θ : FiniteComplexRepresentation.{0, 0} G)
    (hsection : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        θ.character (actualRoot S e ^ h * v) = -1) :
    BlocksInnerProduct θ.character
      (oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n)) = -1 := by
  have hclass : BlocksIsClassFunction θ.character :=
    fun g a => Representation.char_conj θ.representation g a
  rw [innerProduct_of_constant_on_support (squareRootSection (actualRoot S e))
    θ.character _ (-1) (actual_root_odd_power_column_support n hn S e basis ideal
      principal hprincipal root hroot) ((classFunction_section_value_iff hclass).mp hsection)]
  rw [oddPowerPrincipalColumn_principal_pairing basis ideal principal hprincipal,
    actual_root_odd_power_principal_coefficient n hn S e basis principal hprincipal root hroot]
  norm_num


end CFSG.Wreathed.SquareRootSmallCharacterRigidity
