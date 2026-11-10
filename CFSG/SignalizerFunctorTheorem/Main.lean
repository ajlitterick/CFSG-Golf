module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.PrimeTwo
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.FaithfulSimple

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

theorem solvableRankOneTheorem_of_twoThreeCase
    (htt : ∀ p : ℕ, p.Prime → 5 ≤ p → Solvable.TwoThreeCase p 1) : SolvableRankOneTheorem := by
  intro p hp
  by_cases h3 : p ≤ 3
  · exact Solvable.solvableRankOneTheoremAt_of_le_three p hp h3
  · have h4 : p ≠ 4 := fun h => by
      rw [h] at hp
      norm_num at hp
    exact Solvable.solvableRankOneTheoremAt_of_cases p hp (Solvable.fiveCase p 1 hp)
      (htt p hp (by omega))


end CFSG.SignalizerFunctorTheorem
