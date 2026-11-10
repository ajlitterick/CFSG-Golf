module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def L7_1 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ J ∈ Ω, AEmpty Ω J) →
        ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ u r v t : G,
          Subgroup.zpowers u = R ⊓ W → R = Subgroup.closure {u, r} →
          Subgroup.zpowers v = T ⊓ W → T = Subgroup.closure {v, t} →
            (R ⊔ T ⊔ OCW W) ⊓ W = Subgroup.closure {u, v} ∧
            ((∃ J ∈ Ω, R ≤ J ∧ T ≤ J) ∨
              (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaNbr Ω J ∧
                ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W) ∨
              (∃ J ∈ Ω, ∃ J' ∈ Ω, R ≤ J ∧ T ≤ J' ∧ J' ∈ omegaStarNbr Ω J ∧
                J' ∉ omegaNbr Ω J ∧
                ∃ v' : G, Subgroup.zpowers v' = Subgroup.zpowers v ∧
                  t⁻¹ * u * t * (u * v')⁻¹ ∈ OCW W ∧ r⁻¹ * v' * r * (v' * u)⁻¹ ∈ OCW W))

@[expose] def L7_5_2 : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ W ∈ WSet Ω, ∀ W' ∈ WSet Ω, Nonempty (↥(muGroup Ω W) ≃* ↥(muGroup Ω W'))


end CFSG.ClassicalInvolution.Asc77
