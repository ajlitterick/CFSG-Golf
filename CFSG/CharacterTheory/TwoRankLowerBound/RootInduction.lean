module

public import CFSG.CharacterTheory.TwoRankLowerBound.InvolutionRoots

public section

open scoped BigOperators

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def inducedFunction {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (function : subgroup → ℂ) (element : G) : ℂ := by
  classical
  exact (Nat.card subgroup : ℂ)⁻¹ * ∑ conjugator : G,
    if hmember : conjugator⁻¹ * element * conjugator ∈ subgroup then
      function ⟨conjugator⁻¹ * element * conjugator, hmember⟩ else 0


end CFSG.TwoRankLowerBound.Helpers
