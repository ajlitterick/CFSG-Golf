module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props316

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def Lemma33CentralInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ a ∈ normalizer (solomonKStarOf N : Set G), orderOf a = 2 →
      K ≤ centralizer ({a} : Set G) →
      conjClosure K (twoLayerIn (centralizer ({a} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({a} : Set G))) ⊔ K


end CFSG.ComponentClassification.Sol76
