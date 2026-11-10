module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired5

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.MilestoneAssembly

@[expose] def TwinDCase (p f m : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z →
      LocalShapeT p f 2 .POmegaPlus m (CoreAssembly.conjClass K) z →
      ∀ β ∈ CoreAssembly.conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (CoreAssembly.conjClass K) K β z →
          PartnerPatternD p f m (CoreAssembly.conjClass K) K β t

end CFSG.ClassicalInvolution.RouteD
