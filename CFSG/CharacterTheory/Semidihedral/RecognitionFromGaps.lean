module

public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierAssembly
public import CFSG.CharacterTheory.Semidihedral.StationarySevenNineFinal
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.CharacterTheory.Semidihedral.Principal.FieldFactorOneFixedCoreRegular

public section

namespace CFSG.Semidihedral.RecognitionFromGaps

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.SimpleLayerFrontier

theorem sevenNineCoreHypothesis_holds
    : SevenNineCoreHypothesis :=
  @StationarySevenNine.stationary_all_prime_seven_nine_odd_core_is_cyclic_and_central
   

theorem fieldFactorOneHypothesis_holds
    : FieldFactorOneHypothesis :=
  @Principal.actual_field_factor_one_nontrivial_fixed_core_is_regular_and_has_no_inverted_odd_factor
   

theorem stated_model_psl_of_lowTwoRank {G : Type} [Group G] {n p f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL n p f) :
    CFSG.Open.StatedClassicalModel G .PSL n p f := h

theorem stated_model_psu_of_lowTwoRank {G : Type} [Group G] {n p f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU n p f) :
    CFSG.Open.StatedClassicalModel G .PSU n p f := h


theorem semidihedral_recognition_of_local_theorems
    (hB : StationaryCoverageStatement)
    (hF : FieldFactorOneStatement) (hA : FixedCoreNontrivialStatement)
    (hU : UnitaryBranchStatement) (h5 : ParameterFiveRecognitionStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hsd : ∃ (S : Sylow 2 G) (n : ℕ), 4 ≤ n ∧
      Nonempty ((S : Subgroup G) ≃* SemidihedralGroup n)) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
        CFSG.Open.StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
        CFSG.Open.StatedClassicalModel G .PSU 3 p f) ∨
    Nonempty (G ≃* CFSG.Open.StatedM11) := by
  obtain ⟨S, n, hn, ⟨e⟩⟩ := hsd
  have hfront := frontier_of_local_theorems hB hF hA hU h5 sevenNineCoreHypothesis_holds
    fieldFactorOneHypothesis_holds
  have hodd : ∀ l : ℕ, Odd l → l ≠ 2 := by
    rintro l hl rfl
    exact (Nat.not_even_iff_odd.mpr hl) even_two
  rcases semidihedral_simple_model_of_frontier hfront G hnonab n hn S ⟨e.symm⟩ with
    ⟨l, a, hl, hlo, ha, hq, hm⟩ | ⟨l, a, hl, hlo, ha, hq, hm⟩ | hM
  · exact Or.inl ⟨l, a, hl, hodd l hlo, ha, hq, stated_model_psl_of_lowTwoRank hm⟩
  · exact Or.inr (Or.inl ⟨l, a, hl, hodd l hlo, ha, hq, stated_model_psu_of_lowTwoRank hm⟩)
  · exact Or.inr (Or.inr hM)


end CFSG.Semidihedral.RecognitionFromGaps
