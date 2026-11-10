module

public import CFSG.ClassicalInvolution.Balance.Theorem5Fuzzy
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyPair
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames MemberClass FuzzyFrameBalance)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]


@[expose] def FuzzyNoF3 (p f : ℕ) [Fact p.Prime] (𝒞 : MemberClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) →
        ∀ (J₁ J₂ J₃ : Subgroup G) (z₁ z₂ z₃ : G), J₁ ∈ 𝒞 K → J₂ ∈ 𝒞 K → J₃ ∈ 𝒞 K →
          AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃ → ∀ b ∈ triangleAxis z₁ z₂ z₃, b ≠ 1 →
            NoComponentOverF3 p f (triangleSecFamily J₁ J₂ J₃ b) b


end CFSG.ClassicalInvolution.Balance.Bootstrap
