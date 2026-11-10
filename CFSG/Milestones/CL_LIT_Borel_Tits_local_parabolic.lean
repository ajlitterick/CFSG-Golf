module

public import CFSG.LieType.BorelTits.AllModels

public section

universe u v w

namespace CFSG.Open


end CFSG.Open

namespace CFSG.Milestones

theorem cl_lit_borel_tits_local_parabolic_all_models
    (X : Type) [Group X] (t : Assembly.LowTwoRank.StatedLieTag) (n r f : ℕ)
    (hmodel : Blueprint.LieModel X t n r f)
    (U : Subgroup X) (hU : U ≠ ⊥) (hUr : IsPGroup r U) :
    ∃ (S : Sylow r X) (P : Subgroup X), P ≠ ⊤ ∧
      Subgroup.normalizer (U : Set X) ≤ P ∧
      Open.pCoreOf r (Subgroup.normalizer (U : Set X)) ≤ Open.pCoreOf r P ∧ U ≤ Open.pCoreOf r P ∧
      (t ≠ .Tits → Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) ∧
      (t = .Tits → (S : Subgroup X) ≤ P) :=
  LieType.BorelTits.lieModel_conclusion X t n r f hmodel U hU hUr

end CFSG.Milestones
