module

public import CFSG.ClassicalInvolution.Asc77.WP3FramePSCNine
import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

section Chain

variable {p f : ℕ} [Fact p.Prime]

@[expose] def NoTwinsChain (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → ChainShape p f (CoreAssembly.conjClass K) z →
        ∀ M ∈ CoreAssembly.conjClass K, ∀ M' ∈ twinSet (CoreAssembly.conjClass K) M, M' = M

@[expose] def AEmptyChain (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → ChainShape p f (CoreAssembly.conjClass K) z →
        ∀ M ∈ CoreAssembly.conjClass K, AEmpty (CoreAssembly.conjClass K) M


end Chain

end CFSG.ClassicalInvolution.Asc77
