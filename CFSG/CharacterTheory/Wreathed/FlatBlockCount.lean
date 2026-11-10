module

public import CFSG.CharacterTheory.Wreathed.FlatBlockCountLabels
public import CFSG.CharacterTheory.Wreathed.CompatibleBoundaryCount

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.FullDefectLabels
  CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Wreathed.CompatibleFamilies

variable {G : Type*} [Group G] [Fintype G]

theorem card_flatWreathedBlocks [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (η : G)
    (hη : η ∈ Subgroup.normalizer ((Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)),
      wreathModelHom S e (Original.t (2 ^ n))} : Subgroup G) : Set G))
    (hord : orderOf ((Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)),
      wreathModelHom S e (Original.t (2 ^ n))}).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    (flatWreathedBlocks basis ideal S e).card = (boundaryKernel S e η).index := by
  obtain ⟨eb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)))
  obtain ⟨nb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.normalizer ((S : Subgroup G) : Set G))
  obtain ⟨qb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ⧸ boundaryKernel S e η)
  obtain ⟨-, -, -, -, -, hK, -, -, -, -, hcount⟩ :=
    compatible_centralizer_boundary_character_count hnonab n hn S e eb η hη hord qb
  obtain ⟨g, -⟩ := exists_equiv_flatWreathedBlocks basis ideal hn S e eb nb _ rfl
  rw [← Nat.card_eq_finsetCard, ← Nat.card_congr g, Nat.card_coe_set_eq, hK]
  exact hcount


end CFSG.Wreathed
