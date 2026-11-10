module

public import CFSG.ClassicalInvolution.Balance.BootstrapInvolutory
public import CFSG.ClassicalInvolution.Balance.BootstrapLevi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime]

@[expose] def FrameNoF3 (p f : ℕ) [Fact p.Prime] : Prop :=
  p ^ f = 27 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ x y : G, x * y ≠ y * x) → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → RouteD.DeltaConnected (CoreAssembly.conjClass K) →
        ∀ A : Subgroup G, MemberFamily p f (CoreAssembly.conjClass K) A
          (frameFamily p f (CoreAssembly.conjClass K) A) →
        ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f (CoreAssembly.conjClass K) a


end CFSG.ClassicalInvolution.Balance.Bootstrap
