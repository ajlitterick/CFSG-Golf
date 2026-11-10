module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusPattern

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinTDPatternOn (p f : ℕ) [Fact p.Prime] (P : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, P m →
      LocalShapeT p f 2 .POmegaMinus m (conjClass K) z → ∀ β ∈ conjClass K, ∀ t : G,
        IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (conjClass K) K β z → PartnerPatternMinus p f m (conjClass K) K β t


end CFSG.ClassicalInvolution.RouteD.Gaps
