module

public import CFSG.ClassicalInvolution.Balance.Q27D4Balance
import CFSG.ClassicalInvolution.RouteD.NoG2D4Model

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance
open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
open CFSG.Blueprint.Chevalley (TwistTag adjointGroup)

section Facts


@[expose] def InvolutionOddCoreTrivial (K : Type) [Group K] : Prop :=
  ∀ u : K, u * u = 1 → u ≠ 1 → ∀ N : Subgroup K, N ≤ Subgroup.centralizer ({u} : Set K) →
    (∀ c ∈ Subgroup.centralizer ({u} : Set K), ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
      Odd (Nat.card N) → N = ⊥

@[expose] def InvolutionCentralizersGenerate (K : Type) [Group K] : Prop :=
  ∀ u₁ u₂ : K, u₁ * u₁ = 1 → u₂ * u₂ = 1 → u₁ ≠ 1 → u₂ ≠ 1 → u₁ ≠ u₂ → u₁ * u₂ = u₂ * u₁ →
    Subgroup.centralizer ({u₁} : Set K) ⊔ Subgroup.centralizer ({u₂} : Set K) ⊔
      Subgroup.centralizer ({u₁ * u₂} : Set K) = ⊤

end Facts

section Abstract


end Abstract

section Model


end Model

section Reduction


end Reduction

end CFSG.ClassicalInvolution.Balance.Q27
