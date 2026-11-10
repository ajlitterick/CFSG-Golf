module

public import CFSG.LocalAnalysis.StandardType.GGTwoSignalizerRadical
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs


@[expose] def GGOppositeRadicalCountInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      (∃ k : ℕ, Nat.card (ggOppositeRadicals G₀ Q) = 2 ^ k) ∧
        ∀ V ∈ ggOppositeRadicals G₀ Q, Q ⊔ V = G₀


theorem ggTwoSignalizerGenInput_of_oppositeRadicalCount (h : GGOppositeRadicalCountInput) :
    GGTwoSignalizerGenInput := by
  intro G _ _ t n f ψ G₀ hpres p hp hp2 E hEp hEG₀ T hTG₀ hT hT2 hET
  exact GGTwoSig.exists_two_signalizers_of_count hp hp2 hEp hEG₀ hTG₀ hT hT2 hET
    (h G t n f ψ G₀ hpres)

end Inputs

end CFSG.StandardType
