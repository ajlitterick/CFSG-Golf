module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Cover

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinYXOrbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ J ∈ centralizingMembers (𝒞 K) {z}, J ≠ K → J ≠ T →
        ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
          ∃ y ∈ locLayer (𝒞 K) e.u, conjSub y J = N

@[expose] def TwinYNoCentralOn (P : StatedLieTag → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → P tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ M ∈ centralizingMembers (𝒞 K) {e.u},
        ∃ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K ∧ N ≠ T ∧ ¬ Commutes M N

end Statement

section Trans


end Trans

section TypeOfInputs


end TypeOfInputs

end CFSG.ClassicalInvolution.RouteD.TwinY
