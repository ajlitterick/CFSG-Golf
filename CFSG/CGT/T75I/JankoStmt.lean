module

public import CFSG.CGT.T75I.Janko

public section

namespace CFSG.CGT.T75I

open CFSG.CGT.Timmesfeld75


@[expose] def JankoM22CtxInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T T₁ : Subgroup G, IsWC T → Nat.card T = 16 → T ⊓ T₁ = ⊥ →
      (∃ s : G, T₁ = conjSubgroup s T) →
      Nat.card (normIn T T₁) = 4 → Nat.card (normIn T₁ T) = 4 →
      (∀ d ∈ T, d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)) →
      Subgroup.centralizer (T : Set G) = T →
      (∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y) →
      Subgroup.normalizer (T : Set G) ⊔ T₁ = ⊤ →
      Nonempty (NQuot T ≃* alternatingGroup (Fin 6)) →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .M22

@[expose] def JankoM23CtxInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T T₁ : Subgroup G, IsWC T → Nat.card T = 16 → T ⊓ T₁ = ⊥ →
      (∃ s : G, T₁ = conjSubgroup s T) →
      Nat.card (normIn T T₁) = 4 → Nat.card (normIn T₁ T) = 4 →
      (∀ d ∈ T, d ≠ 1 → Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G)) →
      Subgroup.centralizer (T : Set G) = T →
      (∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y) →
      Subgroup.normalizer (T : Set G) ⊔ T₁ = ⊤ →
      Nonempty (NQuot T ≃* alternatingGroup (Fin 7)) →
        CFSG.Blueprint.NativeSporadic.IsSporadic G .M23

end CFSG.CGT.T75I
