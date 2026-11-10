module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore
public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

@[expose] def QuadraticAutomorphism {G : Type u} [Group G] (automorphism : MulAut G) : Prop :=
  ∀ element : G, automorphism (element⁻¹ * automorphism element) = element⁻¹ * automorphism element


@[expose] noncomputable def actionPrimeCore {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] (prime : ℕ) (action : actor →* MulAut acted) : Subgroup actor :=
  (pCore prime (actor ⧸ action.ker)).comap (QuotientGroup.mk' action.ker)

@[expose] def PrimeStableAction {actor : Type u} {acted : Type v} [Group actor] [Group acted]
    (prime : ℕ) (action : actor →* MulAut acted) : Prop :=
  ∀ member : actor, QuadraticAutomorphism (action member) → member ∈ actionPrimeCore prime action


end CFSG.RankThreeEvenClassification.Helpers
