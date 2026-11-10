module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryLinearActions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeCorePreimage
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableConjugatePairs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticLinearIdentities

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v w

theorem linearPrimeStableAction_of_solvable_conjugate_pairs
    {actor : Type u} {field : Type v} {space : Type w}
    [Group actor] [Finite actor] [Group.IsSolvable actor]
    [Field field] [AddCommGroup space] [Module field space]
    (prime : ℕ) (hprime : prime.Prime) (action : actor →* (space ≃ₗ[field] space))
    (hpairs : ∀ member : actor, ((action member : Module.End field space) - LinearMap.id) ^ 2 = 0 →
      PrimeConjugatePairs prime (action.rangeRestrict member)) :
    LinearPrimeStableAction prime action := by
  have : Finite action.range := Finite.of_surjective action.rangeRestrict action.rangeRestrict_surjective
  have : Group.IsSolvable action.range :=
    Group.isSolvable_of_surjective (f := action.rangeRestrict) action.rangeRestrict_surjective
  intro member hquadratic
  rw [primeCore_quotient_preimage_eq_range_preimage]
  exact solvable_conjugate_pair_mem_primeCore prime hprime (action.rangeRestrict member)
    (hpairs member hquadratic)


end CFSG.RankThreeEvenClassification.Helpers
