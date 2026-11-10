module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallFinal
public import CFSG.ClassicalInvolution.RouteD.SmallBWired

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinTDCase (p f m : ℕ) [Fact p.Prime] : Prop :=
  Gaps.TwinTDPatternOn p f fun k => k = m


@[expose] def TwinBCase (p f m : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z →
      LocalShapeT p f 2 .POmegaOdd m (conjClass K) z →
      ∀ β ∈ conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (conjClass K) K β z → PartnerPatternBPair p f m (conjClass K) K β t


end CFSG.ClassicalInvolution.RouteD
