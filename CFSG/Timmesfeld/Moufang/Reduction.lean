module

public import CFSG.Timmesfeld.Moufang.Criterion
public import CFSG.Timmesfeld.Skeleton

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def CommLambda (D : Set G) : Prop :=
  ∀ y ∈ D, ∀ x₁ ∈ D, ∀ x₂ ∈ D, Commute y x₁ → y * x₁ ∈ D → Commute y x₂ → y * x₂ ∈ D →
    orderOf (x₁ * x₂) = 4 → (x₁ * x₂) ^ 2 ∈ rootSet D y


end CFSG.Timmesfeld.Moufang
